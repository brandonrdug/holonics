"""A ruler for the theory panel's writes (the lead, November 22): for each written form (`forms.written`: label, prompt, write), the write's
words (letters and apostrophes, two or more, lower case), the share of them in its slice's lexicon (`lexicon_theory.pkl`: the words met five
times or more in the slice's training documents), whether the write loops (a unit of 1 to 24 bytes repeated to fill its last 48), and the
longest run of bytes it shares with its own prompt (a recitation's mark). Outside the machine. Usage: theory_score.py NAME=DIR ... [show]"""
import sys, re, pickle
lex = pickle.load(open('lexicon_theory.pkl', 'rb'))
def words(t): return re.findall(r"[a-z][a-z']+", t.lower())
def loops(w):
    tail = w[-48:]
    return any(len(tail) >= 2 * u and tail == (tail[:u] * (len(tail) // u + 1))[:len(tail)] for u in range(1, 25))
def shared(w, p):
    best = 0
    for i in range(len(w)):
        for j in range(i + best + 1, len(w) + 1):
            if w[i:j] in p: best = j - i
            else: break
    return best
args = sys.argv[1:]; show = 'show' in args; args = [a for a in args if a != 'show']
for arg in args:
    name, d = arg.split('=')
    by = {}
    for line in open(f'{d}/forms.written'):
        f = line.rstrip('\n').split('\t')
        if len(f) < 3: continue
        label, prompt, write = f[0], f[1].replace('\\n', '\n'), f[2].replace('\\n', '\n')
        s = label.split(':')[0]
        ws = words(write); inlex = sum(1 for x in ws if x in lex[s])
        b = by.setdefault(s, [0, 0, 0, 0, 0])
        b[0] += 1; b[1] += len(ws); b[2] += inlex; b[3] += int(loops(write)); b[4] = max(b[4], shared(write, prompt))
        if show: print(f'{name} {label}: {write!r}')
    print(f'THEORY_PANEL {name} ' + ' | '.join(f'{s}: words {b[1]} in lexicon {b[2]} ({100 * b[2] // max(b[1], 1)}%) loops {b[3]} of {b[0]} longest shared with prompt {b[4]}' for s, b in sorted(by.items())))
