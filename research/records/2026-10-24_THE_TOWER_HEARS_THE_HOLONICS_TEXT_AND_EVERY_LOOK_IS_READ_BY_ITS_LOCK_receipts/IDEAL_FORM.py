"""The one complex situated form the state at B suggests, written as a forms file so the machine's
own founding (FROM) reports its canonical share and its own read reports its values at the probe
cells. a: the complex least-squares read of the first operand's units character
z_1 = exp(2 pi i a0 / 10) from level 0's state before b0 arrives (the B cells of the training
equation block, no constant: the form has none on the state), carried to the face's grain
(before / 2^8). b: the arriving class's factor, chi_1(d) on the ten digits, and on every other
class either free (the least-norm b, "free") or held to zero in the least squares weighted by each
class's count in the training moments ("quiet"). An exterior construction: a ceiling of what this
form's shape can carry, not a founded form."""
import sys, importlib.util
import numpy as np
spec = importlib.util.spec_from_file_location("ch", sys.argv[1]); ch = importlib.util.module_from_spec(spec)
sys.argv = sys.argv[:1]; spec.loader.exec_module(ch)  # the character read's fits (prints its lines again)
head = open("situated7/forms_c1.txt").readline()
X, F = ch.Xt, ch.Ft
A = X
W = np.linalg.solve(A.T @ A + np.eye(A.shape[1]), A.T @ np.stack([np.cos(2*np.pi*F[:,0]/10), np.sin(2*np.pi*F[:,0]/10)], 1))
# x = before / 2^14 and face = before / 2^8, so z^ = W^T x = (W / 2^6)^T face
a = W / 64
a = np.round(a / np.abs(a).max() * 2**14).astype(np.int64)
theta = open("hcont2/STATE.0").read().split("\n")[1].split(" ")
enc = np.array([int(v) for v in theta[:256*64]], dtype=float).reshape(256, 64)
hats = np.hstack([enc, np.full((256, 1), 65536.0)])
counts = np.zeros(256)
for line in open("situated5/train.moments"):
    if line.startswith("CLASS "):
        p = line.split(); counts[int(p[1])] = int(p[2][2:])
digits = np.arange(48, 58)
chi = np.exp(2j*np.pi*np.arange(10)/10)
bs = {}
# free: least-norm b with hat_d . b = chi(d)
bs["free"] = np.linalg.lstsq(hats[digits], chi, rcond=None)[0]
# quiet: digits exact (large weight), every other class pulled to zero by its count
w = counts.copy(); w[digits] = counts.sum() * 1e3
target = np.zeros(256, dtype=complex); target[digits] = chi
sw = np.sqrt(w)[:, None]
bs["quiet"] = np.linalg.lstsq(hats * sw, target * sw[:, 0], rcond=None)[0]
for name, b in bs.items():
    beta = hats @ b
    other = np.setdiff1d(np.arange(256), digits)
    print(f"b {name}: digits' beta error {np.abs(beta[digits]-chi).max():.2e}; count-weighted rms |beta| on other classes {np.sqrt((counts[other]*np.abs(beta[other])**2).sum()/counts[other].sum()):.3f}")
    bi = np.stack([b.real, b.imag]) / np.abs(np.stack([b.real, b.imag])).max() * 2**20
    bi = np.round(bi).astype(np.int64)
    # the release: values at the training B cells brought to about 2^16
    face = np.round(X * 2**6)
    p = face @ a
    pc = p[:,0] + 1j*p[:,1]
    bc = (hats @ (bi[0] + 1j*bi[1]))[48 + F[:,1]]
    rms = np.sqrt(np.mean(np.abs(pc * bc)**2))
    shift = max(0, int(np.ceil(np.log2(rms))) - 16)
    line = f"FORM 0 shift={shift} faces=re,im a={','.join(map(str,a[:,0]))} ai={','.join(map(str,a[:,1]))} b={','.join(map(str,bi[0]))} bi={','.join(map(str,bi[1]))}\n"
    open(f"char/ideal_{name}.txt", "w").write(head + line)
    print(f"wrote char/ideal_{name}.txt shift={shift}")
