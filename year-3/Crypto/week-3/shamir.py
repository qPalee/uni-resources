# This script contains various helper functions to implement (insecure) Shamir secret sharing
# Any implementation based on these functions should be used for prototyping purposes only.


import random


def evaluate_polynomial(coefficients, xval, modulus):
    # Using Horner's rule to avoid explicit exponentiations
    # https://en.wikipedia.org/wiki/Polynomial_evaluation

    result = 0
    for coef in reversed(coefficients):
        result = (coef + xval * result) % modulus
    return result

def modular_inverse(a, modulus):
    if a == 0:
        return 0
    else:
        return pow(a, -1, modulus)


def generate_polynomial(a0,degree, modulus):
    coefficients = [a0] + [random.randrange(modulus) for _ in range(degree)]
    return coefficients

def lagrange_deltai(points, point, modulus):
    constants = [0] * len(points)
    for i in range(len(points)):
        xi = points[i]
        num = 1
        denom = 1
        for j in range(len(points)):
            if j != i:
                xj = points[j]
                num = (num * (xj - point)) % modulus
                denom = (denom * (xj - xi)) % modulus
        constants[i] = (num * modular_inverse(denom, modulus)) % modulus
    return constants

def lagrange_evaluate(coordinates, point, modulus):
    # replace with your code
    secret =0
    return secret

def Stn_share(polynomial, num_parties, modulus):
    # replace with your code
    shares=0
    return shares

def Stn_reconstruct(shares, parties, modulus):
    # replace with your code
    secret = 0
    return secret

# Press the green triangle to run the script, or the bug to debug the script.
if __name__ == '__main__':
    pmod = 11
    num_parties = 3
    threshold = 2

    test_poly = generate_polynomial(4, threshold-1,pmod)
    print(test_poly)
