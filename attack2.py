import time
import random
import logging
from math import ceil
from math import gcd
from math import isqrt
from sage.all import Integer
from sage.all import RR
from sage.all import ZZ
from sage.all import Integer
from sage.all import ZZ , floor
from sage.all import QQ
from sage.all import Sequence
from sage.all import ZZ
from sage.all import gcd
from sage.all import matrix
from sage.all import set_random_seed
from sage.crypto.util import random_blum_prime

logging.basicConfig(filename='ppfe.log', level=logging.DEBUG, format='%(asctime)s - %(levelname)s - %(message)s')


def log_lattice(L):
    """
    Logs a lattice.
    :param L: the lattice
    """
    for row in range(L.nrows()):
        r = ""
        for col in range(L.ncols()):
            if L[row, col] == 0:
                r += "_ "
            else:
                r += "X "
        logging.debug(r)


def create_lattice(pr, shifts, bounds, order="invlex", sort_shifts_reverse=False, sort_monomials_reverse=False):
    """
    Creates a lattice from a list of shift polynomials.
    :param pr: the polynomial ring
    :param shifts: the shifts
    :param bounds: the bounds
    :param order: the order to sort the shifts/monomials by
    :param sort_shifts_reverse: set to true to sort the shifts in reverse order
    :param sort_monomials_reverse: set to true to sort the monomials in reverse order
    :return: a tuple of lattice and list of monomials
    """
    logging.debug(f"Creating a lattice with {len(shifts)} shifts (order = {order}, sort_shifts_reverse = {sort_shifts_reverse}, sort_monomials_reverse = {sort_monomials_reverse})...")
    if pr.ngens() > 1:
        pr_ = pr.change_ring(ZZ, order=order)
        shifts = [pr_(shift) for shift in shifts]

    monomials = set()
    for shift in shifts:
        monomials.update(shift.monomials())

    shifts.sort(reverse=sort_shifts_reverse)
    monomials = sorted(monomials, reverse=sort_monomials_reverse)
    L = matrix(ZZ, len(shifts), len(monomials))
    for row, shift in enumerate(shifts):
        for col, monomial in enumerate(monomials):
            L[row, col] = shift.monomial_coefficient(monomial) * monomial(*bounds)

    monomials = [pr(monomial) for monomial in monomials]
    return L, monomials


def reduce_lattice(L, delta=0.8):
    """
    Reduces a lattice basis using a lattice reduction algorithm (currently LLL).
    :param L: the lattice basis
    :param delta: the delta parameter for LLL (default: 0.8)
    :return: the reduced basis
    """
    logging.info(f"Reducing a {L.nrows()} x {L.ncols()} lattice...")
    return L.LLL(delta)


def reconstruct_polynomials(B, f, modulus, monomials, bounds, preprocess_polynomial=lambda x: x, divide_gcd=True):
    """
    Reconstructs polynomials from the lattice basis in the monomials.
    :param B: the lattice basis
    :param f: the original polynomial (if set to None, polynomials will not be divided by f if possible)
    :param modulus: the original modulus
    :param monomials: the monomials
    :param bounds: the bounds
    :param preprocess_polynomial: a function which preprocesses a polynomial before it is added to the list (default: identity function)
    :param divide_gcd: if set to True, polynomials will be pairwise divided by their gcd if possible (default: True)
    :return: a list of polynomials
    """
    logging.debug(f"Reconstructing polynomials (divide_original = {f is not None}, modulus_bound = {modulus is not None}, divide_gcd = {divide_gcd})...")
    polynomials = []
    for row in range(B.nrows()):
        norm_squared = 0
        w = 0
        polynomial = 0
        for col, monomial in enumerate(monomials):
            if B[row, col] == 0:
                continue
            norm_squared += B[row, col] ** 2
            w += 1
            assert B[row, col] % monomial(*bounds) == 0
            polynomial += B[row, col] * monomial // monomial(*bounds)

        # Equivalent to norm >= modulus / sqrt(w)
        if modulus is not None and norm_squared * w >= modulus ** 2:
            logging.debug(f"Row {row} is too large, ignoring...")
            continue

        polynomial = preprocess_polynomial(polynomial)

        if f is not None and polynomial % f == 0:
            logging.debug(f"Original polynomial divides reconstructed polynomial at row {row}, dividing...")
            polynomial //= f

        if divide_gcd:
            for i in range(len(polynomials)):
                g = gcd(polynomial, polynomials[i])
                # TODO: why are we only allowed to divide out g if it is constant?
                if g != 1 and g.is_constant():
                    logging.debug(f"Reconstructed polynomial has gcd @#$ with polynomial at {i}, dividing...")
                    polynomial //= g
                    polynomials[i] //= g

        if polynomial.is_constant():
            logging.debug(f"Polynomial at row {row} is constant, ignoring...")
            continue

        polynomials.append(polynomial)

    logging.debug(f"Reconstructed {len(polynomials)} polynomials")
    return polynomials


def find_roots_univariate(x, polynomial):
    """
    Returns a generator generating all roots of a univariate polynomial in an unknown.
    :param x: the unknown
    :param polynomial: the polynomial
    :return: a generator generating dicts of (x: root) entries
    """
    if polynomial.is_constant():
        return

    for root in polynomial.roots(multiplicities=False):
        if root != 0:
            yield {x: int(root)}


def find_roots_gcd(pr, polynomials):
    """
    Returns a generator generating all roots of a polynomial in some unknowns.
    Uses pairwise gcds to find trivial roots.
    :param pr: the polynomial ring
    :param polynomials: the reconstructed polynomials
    :return: a generator generating dicts of (x0: x0root, x1: x1root, ...) entries
    """
    if pr.ngens() != 2:
        return

    logging.debug("Computing pairwise gcds to find trivial roots...")
    x, y = pr.gens()
    for i in range(len(polynomials)):
        for j in range(i):
            g = gcd(polynomials[i], polynomials[j])
            if g.degree() == 1 and g.nvariables() == 2 and g.constant_coefficient() == 0:
                # g = ax + by
                a = int(g.monomial_coefficient(x))
                b = int(g.monomial_coefficient(y))
                yield {x: b, y: a}
                yield {x: -b, y: a}


def find_roots_groebner(pr, polynomials):
    """
    Returns a generator generating all roots of a polynomial in some unknowns.
    Uses Groebner bases to find the roots.
    :param pr: the polynomial ring
    :param polynomials: the reconstructed polynomials
    :return: a generator generating dicts of (x0: x0root, x1: x1root, ...) entries
    """
    # We need to change the ring to QQ because groebner_basis is much faster over a field.
    # We also need to change the term order to lexicographic to allow for elimination.
    gens = pr.gens()
    s = Sequence(polynomials, pr.change_ring(QQ, order="lex"))
    while len(s) > 0:
        G = s.groebner_basis()
        logging.debug(f"Sequence length: {len(s)}, Groebner basis length: {len(G)}")
        if len(G) == len(gens):
            logging.debug(f"Found Groebner basis with length {len(gens)}, trying to find roots...")
            roots = {}
            for polynomial in G:
                vars = polynomial.variables()
                if len(vars) == 1:
                    for root in find_roots_univariate(vars[0], polynomial.univariate_polynomial()):
                        roots |= root

            if len(roots) == pr.ngens():
                yield roots
                return
            
            return
        else:
            # Remove last element (the biggest vector) and try again.
            s.pop()


def find_roots_resultants(gens, polynomials):
    """
    Returns a generator generating all roots of a polynomial in some unknowns.
    Recursively computes resultants to find the roots.
    :param polynomials: the reconstructed polynomials
    :param gens: the unknowns
    :return: a generator generating dicts of (x0: x0root, x1: x1root, ...) entries
    """
    if len(polynomials) == 0:
        return

    if len(gens) == 1:
        if polynomials[0].is_univariate():
            yield from find_roots_univariate(gens[0], polynomials[0].univariate_polynomial())
    else:
        resultants = [polynomials[0].resultant(polynomials[i], gens[0]) for i in range(1, len(gens))]
        for roots in find_roots_resultants(gens[1:], resultants):
            for polynomial in polynomials:
                polynomial = polynomial.subs(roots)
                if polynomial.is_univariate():
                    for root in find_roots_univariate(gens[0], polynomial.univariate_polynomial()):
                        yield roots | root


def find_roots_variety(pr, polynomials):
    """
    Returns a generator generating all roots of a polynomial in some unknowns.
    Uses the Sage variety (triangular decomposition) method to find the roots.
    :param pr: the polynomial ring
    :param polynomials: the reconstructed polynomials
    :return: a generator generating dicts of (x0: x0root, x1: x1root, ...) entries
    """
    # We need to change the ring to QQ because variety requires a field.
    s = Sequence([], pr.change_ring(QQ))
    for polynomial in polynomials:
        s.append(polynomial)
        I = s.ideal()
        dim = I.dimension()
        logging.debug(f"Sequence length: {len(s)}, Ideal dimension: {dim}")
        if dim == -1:
            s.pop()
        elif dim == 0:
            logging.debug("Found ideal with dimension 0, computing variety...")
            for roots in I.variety(ring=ZZ):
                yield {k: int(v) for k, v in roots.items()}

            return


def find_roots(pr, polynomials, method="resultants"):
    """
    Returns a generator generating all roots of a polynomial in some unknowns.
    The method used depends on the method parameter.
    :param pr: the polynomial ring
    :param polynomials: the reconstructed polynomials
    :param method: the method to use, can be "groebner", "resultants", or "variety"
    :return: a generator generating dicts of (x0: x0root, x1: x1root, ...) entries
    """
    if pr.ngens() == 1:
        logging.debug("Using univariate polynomial to find roots...")
        for polynomial in polynomials:
            yield from find_roots_univariate(pr.gen(), polynomial)
    else:
        # Always try this method because it can find roots the others can't.
        yield from find_roots_gcd(pr, polynomials)

        if method == "groebner":
            logging.debug("Using Groebner basis method to find roots...")
            yield from find_roots_groebner(pr, polynomials)
        elif method == "resultants":
            logging.debug("Using resultants method to find roots...")
            yield from find_roots_resultants(pr.gens(), polynomials)
        elif method == "variety":
            logging.debug("Using variety method to find roots...")
            yield from find_roots_variety(pr, polynomials)

def modular_bivariate(f, e, m, t, X, Y, roots_method="resultants"):
    """
    Computes small modular roots of a bivariate polynomial.
    More information: Herrmann M., May A., "Maximizing Small Root Bounds by Linearization and Applications to Small Secret Exponent RSA"
    :param f: the polynomial
    :param e: the modulus
    :param m: the amount of normal shifts to use
    :param t: the amount of additional shifts to use
    :param X: an approximate bound on the x roots
    :param Y: an approximate bound on the y roots
    :param roots_method: the method to use to find roots
    :return: a generator generating small roots (tuples of x and y roots) of the polynomial
    """
    f = f.change_ring(ZZ)

    pr = ZZ["x", "y", "z"]
    x, y, z = pr.gens()
    qr = pr.quotient(1 + x * y * y - z)
    Z = X * Y * Y

    logging.debug("Generating shifts...")

    shifts = []
    for k in range(m + 1):
        for i in range(m - k + 1):
            for j in range(2):
                g = x ** i * y ** j * f ** k * e ** (m - k)
                g = qr(g).lift()
                shifts.append(g)

    for k in range(m + 1):
        for i in range(1):
            for j in range(2,2+floor(t*k)):
                h = x ** i * y ** j * f ** k * e ** (m - k)
                h = qr(h).lift()
                shifts.append(h)

    L, monomials = create_lattice(pr, shifts, [X, Y, Z])
    L = reduce_lattice(L)

    pr = f.parent()
    x, y = pr.gens()

    polynomials = reconstruct_polynomials(L, f, None, monomials, [X, Y, Z], preprocess_polynomial=lambda p: p(x, y, 1 + x * y * y))
    for roots in find_roots(pr, polynomials, method=roots_method):
        yield roots[x], roots[y]

def factorize(N, phi):
    """
    Recovers the prime factors from a modulus if Euler's totient is known.
    This method only works for a modulus consisting of 2 primes!
    :param N: the modulus
    :param phi: Euler's totient, the order of the multiplicative group modulo N
    :return: a tuple containing the prime factors, or None if the factors were not found
    """
    s = N + 1 - phi
    logging.info(f"phi = {phi}")
    d = s ** 2 - 4 * N
    p = abs(int(s - isqrt(d)) // 2)
    q = abs(int(s + isqrt(d)) // 2)
    return p, q 


def attack(N, e, p0, q0, known_bit_length, factor_bit_length, delta=0.25, m=1, t=None):
    """
    Recovers the prime factors if the private exponent is too small.
    This implementation exploits knowledge of least significant bits of prime factors, if available.
    More information: Boneh D., Durfee G., "Cryptanalysis of RSA with Private Key d Less than N^0.292"
    :param N: the modulus
    :param e: the public exponent
    :param factor_bit_length: the bit length of the prime factors
    :param delta: a predicted bound on the private exponent (d < N^delta) (default: 0.25)
    :param m: the m value to use for the small roots method (default: 1)
    :param t: the t value to use for the small roots method (default: automatically computed using m)
    :return: a tuple containing the prime factors
    """
    A = N+2*p0+2*q0+1
    B = N**2+(p0+q0-1)*N+(p0+q0)**2+p0+q0+1
    x, y = ZZ["x", "y"].gens()
    f = x * (B + A*y + y**2) + 1
    X = Integer(RR(e) * RR(N) ** (delta-2))
    Y = Integer(2 ** int(factor_bit_length + 1))
    beta=(factor_bit_length-known_bit_length)/(factor_bit_length*2)
    logging.debug(f"(2 - delta-2*beta)/beta={(2 - delta-2*beta)/beta}")
    logging.info(f"beta={beta}")
    if (2 - delta-2*beta)/beta>1:
        t=1
    elif (2 - delta-2*beta)/beta<0:
        t=0
    else:
        t = (2 - delta-2*beta)/beta
    logging.info(f"Trying m = {m}, t = {t}...")
    for x_, y_ in modular_bivariate(f, e, m, t, X, Y):
        logging.debug(f"Trying x = {x_}, y = {y_}...")
        z = int(f(x_, y_))
        if z % e == 0:
            logging.debug(f"Verify z = {z}, trying to factorize...")
            phi = N - (y_+p0+q0) + 1
            factors = factorize(N, phi)
            return factors

    return None, None

def generate_RSA_instance(known_bit_length, modulus_bit_length, delta, seed=None, max_attempts=10):
    """
    Generate an RSA instance with given bit-lengths of the modulus and private key d
    :param known_bit_length: the bit length of the known MSBs of p
    :param modulus_bit_length: the bit length of the modulus
    :param delta: a given size on the private exponent (d is roughly N^delta)
    :param seed: the seed for the random number generator
    :param max_attempts: the maximum amount of attempts to generate an RSA instance
    :return: a tuple containing the public key (N, e)
    """
    attempts = 0
    e = d = N = Integer(1)
    d_bit_length = ceil(modulus_bit_length * delta)
    logging.info(f"Generating RSA instance with {modulus_bit_length}-bit modulus and {d_bit_length}-bit private key d...")
    while attempts < max_attempts:
        if seed is None:
            seed = int(time.time() * 1e6)
        set_random_seed(seed)
        prime_bit_length = modulus_bit_length // 2
        p = random_blum_prime(2**(prime_bit_length - 1), 2**prime_bit_length - 1)
        q = random_blum_prime(2**(prime_bit_length - 1), 2**prime_bit_length - 1)
        N = p * q
        p0=p-random.randint(2**(prime_bit_length-known_bit_length-1),2**(prime_bit_length-known_bit_length)-1)
        q0=N//p0
        key = (p**2+p+1)*(q**2+q+1)
        d = random_blum_prime(2**(d_bit_length - 1), 2**d_bit_length - 1)
        e = pow(d, -1, key)
        if N.nbits() != modulus_bit_length and d.nbits() != d_bit_length:
            attempts += 1
            seed = int(time.time() * 1e6)
            logging.info(f"Regenerated seed: {seed}")
        else:
            logging.info(f"Geenerated gifp instance successfully with seed: {seed}") 
            logging.debug(f"Generated RSA instance with N = {N}")
            logging.debug(f"Generated RSA instance with e = {e}")
            logging.debug(f"Generated RSA instance with d = {d}")
            logging.debug(f"Generated RSA instance with p = {p}")
            logging.debug(f"Generated RSA instance with q = {q}")
            logging.debug(f"Generated RSA instance with p0 = {p0}")
            logging.debug(f"Generated RSA instance with q0 = {q0}")
        return N, e, p0, q0
    logging.warning(f"Failed to generate RSA instances after {max_attempts} attempts.")
    return None, None, None, None

def attack_RSA_instance(known_bit_length,modulus_bit_length, m, delta, seed=None, max_attempts=10):
    """
    Attack an RSA instance with given bit-lengths of the modulus and private key d
    :param modulus_bit_length: the bit length of the modulus
    :param m: a given parameter for controlling the lattice dimension
    :param delta: a given size on the private exponent (d is roughly N^delta)
    :param seed: the seed for the random number generator
    :param max_attempts: the maximum amount of attempts to generate an RSA instance
    :return: 1 if attack succeeds else 0
    """
    N, e ,p0, q0 = generate_RSA_instance(known_bit_length,modulus_bit_length, delta)
    logging.debug(f"Generated RSA instance with known_bit_length = {known_bit_length}")
    logging.info(f"Starting Boneh-Durfee attack...")
    p_bits = modulus_bit_length / 2
    p, q = attack(N, e,p0,q0, known_bit_length,p_bits, delta, m)
    if p is not None and q is not None:
        logging.info(f"Succeeded!")
        logging.info(f"Found p = {p}")
        logging.info(f"Found q = {q}")
        return 1
    else:
        logging.info(f"Failed!")
        return 0

def attack2(test_times, known_bit_length, modulus_bit_length, m, delta, seed=None, max_attempts=10):
    """
    Attack an RSA instance with given bit-lengths of the modulus and private key d
    :param modulus_bit_length: the bit length of the modulus
    :param m: a given parameter for controlling the lattice dimension
    :param delta: a given size on the private exponent (d is roughly N^delta)
    :param seed: the seed for the random number generator
    :param max_attempts: the maximum amount of attempts to generate an RSA instance
    """
    logging.info(f"Test for delta={delta} with {test_times} times:")
    total_time = 0
    results = []
    for i in range(test_times):
        start_time = time.time()
        result = attack_RSA_instance(known_bit_length,modulus_bit_length, m, delta, seed=seed, max_attempts=10)
        end_time = time.time()
        test_time = end_time - start_time
        if result:
            total_time += test_time
            results.append(result)
        logging.info(f"Test {i+1} costs {test_time:.6f} seconds")
    if len(results) == 0:
        logging.info(f"Failed to recover factors in {test_times} times")
        print(f"Failed to recover factors in {test_times} times")
    else:
        avg_time = total_time / len(results)
        logging.info(f"The success rate for delta={delta} using m={m} is {sum(results)/test_times*100}% and average time is {avg_time:.6f} seconds")
        print(f"The success rate for delta={delta} using m={m} is {sum(results)/test_times*100}% and average time is {avg_time:.6f} seconds")

# Test the attack
p_bits = 256
modulus_bit_length = p_bits * 2
known_bit_length=p_bits//8
delta = 0.428
test_times = 10
m = 3
seed= 1713096832377779
attack2(test_times, known_bit_length, modulus_bit_length, m, delta, seed=seed, max_attempts=10)

# The success rate for delta=0.428 using m=3 is 30.0% and average time is 6.174174 seconds