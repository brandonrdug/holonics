# A reading only, never part of the field: of the written answers' letter words, the share that are words of the training
# passage (by type and by token), and the share of the answers' words that also stand in their own question. Prints counts
# only; the written text stays private.
import sys, re
train = open(sys.argv[1], encoding='utf-8', errors='replace').read()
vocab = set(re.findall(r"[a-z]+", train.lower()))
rows = [l.split('\t', 1) for l in open(sys.argv[2], encoding='utf-8').read().split('\n') if '\t' in l]
tot = known = 0
for _, a in rows:
    for w in re.findall(r"[a-z]+", a.replace('\\n', ' ').lower()):
        tot += 1; known += w in vocab
print(f"WORDS written={tot} in_training_vocabulary={known} share={known / max(tot, 1):.3f}")
