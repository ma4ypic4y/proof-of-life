#!/usr/bin/env python3
"""Prompt soup — Computational Life where the chemistry is a language model.

BFF glues two byte strings into one tape, runs it, and splits it back: code
and data share one medium, so programs rewrite one another. Here the medium is
text and the interpreter is an instruction-tuned LLM:

  * the soup is N short texts, initialised as random English words (noise);
  * every epoch the soup is randomly paired; in each pair (A, B) the model is
    run with A as the system prompt and B as the user message, and its reply
    (cut to --max-chars) overwrites B. A is left untouched: it is the "code"
    acting on "data". With --orient user the roles of the two texts in the
    chat are swapped (A is the user message) but the reply still overwrites B:
    a positive control, since a chat model answers the user;
  * no goal, no fitness, no selection. Only interaction.

A text *replicates* if, as a system prompt, it makes the model write a copy of
itself into its partner's slot. Several worlds run in lockstep so that one
batched generation serves all of them. World w uses random.Random(seed + w)
for pairing (and initial noise); sampling is seeded once with mx.random.seed.

usage: prompt_soup.py --out DIR [--seed S] [--worlds K] [--n 128] [--epochs 200]
       [--load RUN_DIR --from-epoch E]   # replays: K futures of one saved soup
"""
import argparse, json, os, random, re, time

import mlx.core as mx
from mlx_lm import batch_generate, load
from mlx_lm.sample_utils import make_sampler

ap = argparse.ArgumentParser()
ap.add_argument("--out", required=True)
ap.add_argument("--seed", type=int, default=0)
ap.add_argument("--worlds", type=int, default=1)
ap.add_argument("--n", type=int, default=128)
ap.add_argument("--epochs", type=int, default=200)
ap.add_argument("--model", default="mlx-community/Qwen2.5-1.5B-Instruct-4bit")
ap.add_argument("--temp", type=float, default=0.7)
ap.add_argument("--max-chars", type=int, default=160)
ap.add_argument("--max-tokens", type=int, default=40)
ap.add_argument("--words", type=int, default=12)
ap.add_argument("--orient", choices=["system", "user"], default="system",
                help="system: A is the system prompt, B the user message (default). "
                     "user: A is the user message, B the system prompt (positive control).")
ap.add_argument("--load", help="replay: start every world from this run's soup")
ap.add_argument("--from-epoch", type=int, default=0)
ap.add_argument("--resume", action="store_true",
                help="continue each world of --out from the last epoch in its soup.jsonl "
                     "(pairing RNG is re-seeded as seed + world + 1000*epoch; sampling as seed + epoch)")
args = ap.parse_args()

model, tok = load(args.model)
resume_epoch = None
if args.resume:
    lasts = []
    for w in range(args.worlds):
        rows = open(os.path.join(args.out, f"w{args.seed + w}", "soup.jsonl")).read().splitlines()
        lasts.append(json.loads(rows[-1])["epoch"])
    resume_epoch = min(lasts)
    args.from_epoch = resume_epoch
mx.random.seed(args.seed if resume_epoch is None else args.seed + resume_epoch)
sampler = make_sampler(temp=args.temp)
WORDS = sorted({w.strip() for w in open("/usr/share/dict/words")
                if w.strip().isalpha() and w.strip().islower() and 3 <= len(w.strip()) <= 9})


def clean(s):
    return re.sub(r"\s+", " ", s).strip()[: args.max_chars]


worlds = []
for w in range(args.worlds):
    seed = args.seed + w
    rng = random.Random(seed if resume_epoch is None else seed + 1000 * resume_epoch)
    d = os.path.join(args.out, f"w{seed}")
    if resume_epoch is not None:
        rows = [json.loads(l) for l in open(os.path.join(d, "soup.jsonl"))]
        rows = [r for r in rows if r["epoch"] <= resume_epoch]
        soup = list(rows[-1]["texts"])
        log = open(os.path.join(d, "soup.jsonl"), "w")
        for r in rows:
            log.write(json.dumps(r) + "\n")
        log.flush()
        json.dump(dict(vars(args), world_seed=seed, resumed_at=resume_epoch),
                  open(os.path.join(d, f"meta_resume_{resume_epoch}.json"), "w"), indent=1)
        worlds.append(dict(seed=seed, rng=rng, soup=soup, log=log))
        continue
    if args.load:
        rows = [json.loads(l) for l in open(os.path.join(args.load, "soup.jsonl"))]
        soup = list(next(r["texts"] for r in rows if r["epoch"] == args.from_epoch))
    else:
        soup = [" ".join(rng.choice(WORDS) for _ in range(args.words)) for _ in range(args.n)]
    d = os.path.join(args.out, f"w{seed}")
    os.makedirs(d, exist_ok=True)
    json.dump(dict(vars(args), world_seed=seed), open(os.path.join(d, "meta.json"), "w"), indent=1)
    log = open(os.path.join(d, "soup.jsonl"), "w")
    log.write(json.dumps({"epoch": args.from_epoch, "texts": soup}) + "\n")
    worlds.append(dict(seed=seed, rng=rng, soup=soup, log=log))

end_epoch = args.epochs if resume_epoch is not None else args.from_epoch + args.epochs
for epoch in range(args.from_epoch, end_epoch):
    t0 = time.time()
    prompts, where = [], []
    for wi, W in enumerate(worlds):
        perm = list(range(len(W["soup"])))
        W["rng"].shuffle(perm)
        W["pairs"] = [(perm[2 * k], perm[2 * k + 1]) for k in range(len(perm) // 2)]
        for a, b in W["pairs"]:
            sys_text, user_text = (W["soup"][a], W["soup"][b]) if args.orient == "system" else (W["soup"][b], W["soup"][a])
            prompts.append(tok.apply_chat_template(
                [{"role": "system", "content": sys_text},
                 {"role": "user", "content": user_text}], add_generation_prompt=True))
            where.append((wi, b))
    out = batch_generate(model, tok, prompts, max_tokens=args.max_tokens, sampler=sampler,
                         completion_batch_size=len(prompts), prefill_batch_size=32)
    for (wi, b), text in zip(where, out.texts):
        worlds[wi]["soup"][b] = clean(text)
    for W in worlds:
        W["log"].write(json.dumps({"epoch": epoch + 1, "pairs": W["pairs"], "texts": W["soup"]}) + "\n")
        W["log"].flush()
    print(f"epoch {epoch + 1}: {time.time() - t0:.1f}s distinct="
          + ",".join(str(len(set(W["soup"]))) for W in worlds), flush=True)
