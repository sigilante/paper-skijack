"""Check for note B2, theorem 3: behavioural lift exists at the Cantor type (Nat -> Bool) -> Bool.

L F = App <EvalT> (liftTree (tree F)) where
  tree F   tabulates a total F : Cantor -> Bool by Berger's search: if F is constant (decided by
           exhaustive search over Cantor space) emit Leaf (F zeros), else split on the head bit;
  liftTree is lift at the data type Tree (lift_D: canonical code from the case form);
  <EvalT>  is the compile-time quotation of a level-0 name (box intro with empty runtime context).
So L F is a code whose read-back v' satisfies v' a = F a on every stream, and extensionally equal
F's get the *same* code (canonicalization). Everything below is closed {S,K,I}; the only
quotation is <EvalT>, <Leaf>, <Node>, <K>, <K I> at compile time.
Reducer: graph reduction (sharing), free variables as inert heads. Standalone, no dependencies."""
import sys, time, itertools
sys.setrecursionlimit(1_000_000)

def app(*xs):
    t = xs[0]
    for x in xs[1:]: t = (t, x)
    return t
def free_in(x, t):
    if isinstance(t, tuple): return free_in(x, t[0]) or free_in(x, t[1])
    return t == x
def absx(x, m):
    if m == x: return 'I'
    if not free_in(x, m): return ('K', m)
    f, a = m
    if a == x and not free_in(x, f): return f
    return (('S', absx(x, f)), absx(x, a))
def lam(xs, body):
    for x in reversed(xs.split() if ' ' in xs else list(xs)): body = absx(x, body)
    return body
def let(x, v, body): return (lam(x, body), v)
def size(t): return size(t[0]) + size(t[1]) if isinstance(t, tuple) else 1
def subst(t, env):
    if isinstance(t, tuple): return (subst(t[0], env), subst(t[1], env))
    return env.get(t, t)

# ---------- graph reducer ----------
STEPS = [0]
def build(t, memo):
    k = id(t)
    if k in memo: return memo[k]
    n = ['@', build(t[0], memo), build(t[1], memo)] if isinstance(t, tuple) else [t]
    memo[k] = n; return n
def whnf(node, cap=5 * 10**8):
    stack = []
    while True:
        while True:
            k = node[0]
            if k == '@': stack.append(node); node = node[1]
            elif k == '>': node = node[1]
            else: break
        n = len(stack)
        if k == 'I' and n >= 1:
            top = stack.pop(); x = top[2]; top[0] = '>'; top[1] = x; del top[2:]; node = top
        elif k == 'K' and n >= 2:
            a = stack.pop(); b = stack.pop(); x = a[2]; b[0] = '>'; b[1] = x; del b[2:]; node = b
        elif k == 'S' and n >= 3:
            a = stack.pop(); b = stack.pop(); c = stack.pop()
            f, g, x = a[2], b[2], c[2]
            c[0] = '@'; c[1] = ['@', f, x]; c[2] = ['@', g, x]; node = c
        else:
            return k, [s[2] for s in reversed(stack)]
        STEPS[0] += 1
        if STEPS[0] > cap: raise RuntimeError('cap')
def gapp(f, *xs):
    for x in xs: f = ['@', f, x]
    return f
def g(t): return build(t, {})

# ---------- object level: Scott encoding of terms (as quine.py / Requote.lean) ----------
encS = lam('abcd', 'a'); encK = lam('abcd', 'b'); encI = lam('abcd', 'c')
AppC = lam('mnabcd', app('d', 'm', 'n'))
def enc(t):
    if t == 'S': return encS
    if t == 'K': return encK
    if t == 'I': return encI
    return app(AppC, enc(t[0]), enc(t[1]))
def decode(node):
    h, args = whnf(gapp(node, ['a'], ['b'], ['c'], ['d']))
    if not args and h in 'abc': return {'a': 'S', 'b': 'K', 'c': 'I'}[h]
    if h == 'd' and len(args) == 2: return (decode(args[0]), decode(args[1]))
    raise ValueError('not a datum')

# ---------- the program ----------
A = lam('xy', app('y', app('x', 'x', 'y'))); Theta = (A, A)
def fix(f, body): return (Theta, absx(f, body))
T, F = 'K', ('K', 'I')
NOT = lam('b', app('b', F, T))
EQB = lam('xy', app('x', 'y', app(NOT, 'y')))
CONS = lam('htk', app('k', 'h', 't'))
HD = lam('s', app('s', T)); TL = lam('s', app('s', F))
ZEROS = fix('z', app(CONS, F, 'z'))
# Berger: find p = let l = cons 0 (find (p . cons 0)) in if p l then l else cons 1 (find (p . cons 1))
FIND = fix('f', lam('p', let('l', app(CONS, F, app('f', lam('a', app('p', app(CONS, F, 'a'))))),
                             app('p', 'l', 'l', app(CONS, T, app('f', lam('a', app('p', app(CONS, T, 'a')))))))))
FORSOME = lam('p', app('p', app(FIND, 'p')))
FOREVERY = lam('p', app(NOT, app(FORSOME, lam('a', app(NOT, app('p', 'a'))))))
CONST = lam('q', let('c', app('q', ZEROS), app(FOREVERY, lam('a', app(EQB, app('q', 'a'), 'c')))))
LEAF = lam('bln', app('l', 'b')); NODE = lam('xyln', app('n', 'x', 'y'))
TREE = fix('tr', lam('q', app(CONST, 'q', app(LEAF, app('q', ZEROS)),
                              app(NODE, app('tr', lam('a', app('q', app(CONS, F, 'a')))),
                                        app('tr', lam('a', app('q', app(CONS, T, 'a'))))))))
EVALT = fix('ev', lam('t s', app('t', 'I', lam('x y', app(HD, 's', app('ev', 'y', app(TL, 's')),
                                                                  app('ev', 'x', app(TL, 's')))))))
LIFTB = lam('b', app('b', enc(T), enc(F)))
LIFTT = fix('lt', lam('t', app('t', lam('b', app(AppC, enc(LEAF), app(LIFTB, 'b'))),
                              lam('x y', app(AppC, app(AppC, enc(NODE), app('lt', 'x')), app('lt', 'y'))))))
LIFT = lam('q', app(AppC, enc(EVALT), app(LIFTT, app(TREE, 'q'))))

# ---------- test functionals (total on Cantor space) ----------
def nth(i, s='a'):
    for _ in range(i): s = app(TL, s)
    return app(HD, s)
OR = lam('xy', app('x', T, 'y')); XOR = lam('xy', app('x', app(NOT, 'y'), 'y'))
FUNS = {
  'const T':         lam('a', T),
  'a0 or not a0':    lam('a', app(OR, nth(0), app(NOT, nth(0)))),        # = const T, other code
  'a0':              lam('a', nth(0)),
  'a0 == T':         lam('a', app(EQB, nth(0), T)),                     # = a0, other code
  'a0 xor a2':       lam('a', app(XOR, nth(0), nth(2))),
  'a0 ? a1 : a3':    lam('a', app(nth(0), nth(1), nth(3))),             # modulus varies with input
  'not not (a0?a1:a3)': lam('a', app(NOT, app(NOT, app(nth(0), nth(1), nth(3))))),
  'a1 ? a0 : a0':    lam('a', app(nth(1), nth(0), nth(0))),             # = a0, reads a1 needlessly
  'parity a0..a5':   lam('a', app(XOR, nth(0), app(XOR, nth(1), app(XOR, nth(2), app(XOR, nth(3), app(XOR, nth(4), nth(5))))))),
  'leading ones >= 5': lam('a', app(nth(0), app(nth(1), app(nth(2), app(nth(3), nth(4), F), F), F), F)),
}
def stream_term(bits, tail):   # finite prefix then a constant or alternating tail
    if tail == 'zeros': s = ZEROS
    elif tail == 'ones': s = fix('z', app(CONS, T, 'z'))
    else: s = fix('z', app(CONS, T, app(CONS, F, 'z')))
    for b in reversed(bits): s = app(CONS, T if b else F, s)
    return s
def bool_of(t):
    h, args = whnf(gapp(g(t), ['x'], ['y']))
    assert not args and h in 'xy', 'not a bool'
    return h == 'x'

def show(t):
    if not isinstance(t, tuple): return t
    f, a = t; sa = show(a)
    return show(f) + ' ' + ('(' + sa + ')' if isinstance(a, tuple) else sa)

codes = {}
print(f'sizes: FIND {size(FIND)}, TREE {size(TREE)}, LIFT {size(LIFT)}, <EvalT> {size(enc(EVALT))}')
for name, q in FUNS.items():
    STEPS[0] = 0; t0 = time.time()
    v = decode(g(app(LIFT, q)))                    # the code L F, read back as a term
    n_lift = STEPS[0]
    assert v[0] == EVALT, 'code is not EvalT applied to a tree'
    codes[name] = v
    ok = 0
    for k in range(0, 8):
        for bits in itertools.product([0, 1], repeat=k):
            for tail in ('zeros', 'ones', 'alt'):
                s = stream_term(list(bits), tail)
                assert bool_of(app(v, s)) == bool_of(app(q, s)), (name, bits, tail)
                ok += 1
    print(f'{name:22s} lift: {n_lift:>10,} contractions, |code| {size(v):>6} atoms, '
          f'agrees with F on {ok} streams  [{time.time()-t0:.1f}s]')

def same(a, b): return codes[a] == codes[b]
for a, b in [('const T', 'a0 or not a0'), ('a0', 'a0 == T'), ('a0', 'a1 ? a0 : a0'),
             ('a0 ? a1 : a3', 'not not (a0?a1:a3)')]:
    assert same(a, b), (a, b)
    print(f'canonical: code({a}) == code({b})')
assert not same('a0', 'a0 xor a2') and not same('a0', 'const T')
print('distinct functionals get distinct codes: ok')
