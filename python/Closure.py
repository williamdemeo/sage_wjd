# This file contains a collection of Python functions for
# computing the "closure" of a set of partitions. This
# means the following:
#
# Let X be the set {0, 1, ..., N-1} and let P be a collection of
# partitions of this set. The "closure of P" is found as follows:
#
# 1. Compute lambda(P) = the set of all unary maps on X that preserve
#    all partitions in P.
#
#    (A unary map f on X is said to preserve a partition p if
#       x, y in same block of p  ==>  f(x), f(y) in same block of p.)
#
# 2. Compute rho(lambda(P)) = the set of all partitions that are
#    preserved by all unary maps in lambda(P).
#
# The result, rho(lambda(P)), is called the closure of P.  This can
# be useful for finding congruence lattices of finite algebras because
# of the following:
#
# Theorem: If rho(lambda(P)) = P, then P is the congruence lattice
#          of the algebra (X, lambda(P)).
#
# Author: williamdemeo@gmail.com
# Date: 2013.04.24


# Convert a partition to a function.
# INPUT
#        p: a list of blocks; e.g. p=[[0,1,2], [3,5], [4,6]]
# OUTPUT
#        h: the corresponding function (with kernel p); e.g. h = [0, 0, 0, 3, 4, 3, 4]
# 
def partition_to_function(p):
    N = max(max(p));
    h = range(N+1);
    for b in p:
        m = min(b)
        for i in b:
            h[i]=m
    return h


# Check whether each function in a set (F) respects a partial function (h).
# INPUT
#        F: a list of unary functions on {0, 1, ..., N-1}, for some integer N.
#            e.g., the list [[0,1,2,3], [0,1,1,0]] represents:
#                  the identity function f(x) = x, and
#                  the map f(0)=0, f(1)=1, f(2)=1, f(3)=0
#
#        h: a partition given as a function;
#           e.g. h=partition_to_function([[0,1,2],[3,5],[4,6]])
#
# OUTPUT
#        True:  if each function (in F) respects the partition (h).
#        False: otherwise
#
def respects(F,h):
    n = len(h)
    for f in F:
        for x in range(n):
            fx = f[x]
            fhx = f[h[x]]

            # Test whether f respects h.
            # (Recall, f respects h if and only if h(f(h(x)) = h(f(x)) for all x.)
            if fx<n and fhx<n and h[fhx]!=h[fx]: return False
            
    return True


# Check whether each function in a set (P) is respected by a partial function (f).
# INPUT
#        f: a partial unary function on {0, 1, ..., N-1}.
#
#        P: a list of unary functions on {0, 1, ..., N-1}, for some integer N.
#            e.g., the list [[0,1,2,3], [0,1,1,0]] represents
#                  the partitions |0|1|2|3| and |0,3|1,2|
#
# OUTPUT
#        True:  if each function (in P) is respects the partial function (f).
#        False: otherwise
#
def respected(f,P):
    n = len(f)
    for h in P:
        for x in range(n):
            # Test whether f respects h.
            # (Recall, f respects h if and only if h(f(h(x)) = h(f(x)) for all x.)
            if h[x]<n and h[f[h[x]]]!=h[f[x]]: return False
    return True


# Lambda returns all functions that respect the partitions in a given set.
# A more standard name for this operation is Fix, so Lambda is just a wrapper function
# (to remind me what Fix does).
#
def Lambda(F, P, f):
    return Fix(F, P, f)


# Rho returns all partitions respected by all unary functions in a given set.
# A more standard name for this operation is Inv, so Rho is just a wrapper function
# (to remind me what Inv does).
def Rho(F, P, p):
    return Inv(F, P, p)


# Recursively build a list (F) of all functions that respect the partitions in a given set (P).
#
# INPUT
#         F: list of unary functions that are known to respect all partitions in P.
#         P: list of functions representing partitions of the set {0, 1, ..., N-1}.
#         f: candidate partial function from a subset of {0, 1, ..., N-1} into {0, 1, ..., N-1}
#            that is known to, so far, respect each partition in P.
#            (a partial function because this routine recursively builds each function f)
#
def Fix(F,P,f):
    n = len(f)
    if n==len(P[0]):
        F.append(f)
        return F
    for x in range(n+1):
        if x==n or x==f[x]:
            b = f+[x]
            if respected(b, P): F = Fix(F,P,b)
    return F


# Recursively build the list of all functions (representing partitions) that are
# respected by all functions in F.
#
# INPUT
#         F: list of unary functions on {0, 1, ..., N-1}, for some integer N.
#         P: list of functions (representing partitions of {0, 1, ..., N-1}) that are known to
#            respect all functions in F.
#         p: candidate partial function from a subset of {0, 1, ..., N-1} into {0, 1, ..., N-1}
#            that is known to be, so far, respected by each function in F.
#            (a partial function because this routine recursively builds each function p)
#
# OUTPUT
#        P: list of functions representing all partitions respected by the functions in F.
def Inv(F,P,p):
    n = len(p)
    if n==len(F[0]):
        P.append(p)
        return P
    for x in range(n+1):
        if x==n or x==p[x]:
            b = p+[x]
            if respects(F,b):
                P = Inv(F,P,b)
    return P


# Check if one function (f) is less than or equal to another function (g),
# according to the partial ordering of functions given by:
#
#   f is less or equal g   iff   kernel(f) is contained in kernel(g)
#
# Equivalently: f is less or equal g iff  (for all x) g(f(x))=g(x)
#
def is_leq(f,g):
    for x in range(len(f)):
        if g[f[x]]!=g[x]:
            return False
    return True


def set_up():
    a = [[0,6,12,18,24],[1,7,13,19,25],[2,8,14,20,26], [3,9,15,21,27], [4,10,16,22,28], [5,11,17,23,29]]
    b = [[0,10,20], [1,11,21], [2,12,22], [3,13,23], [4,14,24], [5,15,25], [6,16,26], [7,17,27], [8,18,28], [9,19,29]]
    c = [[0,15], [1,16], [2,17], [3,18], [4,19], [5,20], [6,21], [7,22], [8,23], [9,24], [10,25], [11,26], [12,27], [13,28], [14,29]] 

