# This file contains a collection of Python functions for
# working with partitions and equivalence relations and,
# in particular, for checking whether relations permute.
#
# We want to answer the following question:
# If L is a lattice of equivalence relations isomorphic to M_n
# for some n, and if at least three atoms pairwise permute,
# must all of the atoms pairwise permute?
#
# williamdemeo@gmail.com
# 2013.05.27

from collections import deque

# Convert a partition to a function.
# INPUT
#        p: a list of blocks; e.g. p=[[0,1,2], [3,5], [4,6]]
# OUTPUT
#        h: the corresponding function (with kernel p); e.g. h = [0, 0, 0, 3, 4, 3, 4]
# 
def partition_to_function(p):
    N = max(max(p))+1;
    h = range(N);
    for b in p:
        m = min(b)
        for i in b:
            h[i]=m
    return h


# Convert a partition to an equivalence relation.
# INPUT
#        p: a list of blocks; e.g. p=[[0,1,2], [3,5], [4,6]]
# OUTPUT
#        r: the corresponding equivalence relation;
#           e.g. r = [[0,0], [1,1], ..., [0,1], [1,0],..., [4,6], [6,4]]
# 
def partition_to_relation(p):
    N = max(max(p))+1;
    r = [];
    for i in range(N):
        for j in range(N):
            if are_related(p,i,j):
                r.append([i,j])
    return r

# Convert an equivalence relation to a partition
# INPUT
#        r: an equivalence relation;
#           e.g. r = [[0,0], [1,1], ..., [0,1], [1,0],..., [4,6], [6,4]]
# OUTPUT
#        p: the corresponding list of blocks; e.g. p=[[0,1,2], [3,5], [4,6]]
# 
def relation_to_partition(r):
    if not (is_reflexive(r) and is_symmetric(r) and is_transitive(r)):
        print 'Error: Input must be an equivalence relation.'
        return false
    N = max(max(r))+1
    p = []
    accounted_for = []
    remaining = range(N)
    for i in range(N):
        if not i in accounted_for:
            accounted_for.append(i)
            iblock = [i]
            for j in range(i+1,N):
                if not j in accounted_for and are_related(r,i,j):
                    accounted_for.append(j)
                    iblock.append(j)
            p.append(iblock)
    return p

            
    # while not len(remaining)==0:
    #     i = remaining.pop(0)
    #     iblock = [i]
    #     for j in range(N):
    #         if j in remaining and are_related(r,i,j):
    #             remaining.remove(j)
    #             iblock.append(j)
    #     p.append(iblock)
    # return p


# return the n-fold composition of the partitions p and q
def compose_n(p, q, n):
    if (n<1):
        print 'Error: Third argument must be a positive integer.'
        return false
    if (n==1):
        return p
    return compose(p, compose(q, p, n-1))


def compose(p, q):
    comp = []
    N = max(max(q))+1
    if not N==max(max(p))+1:
        print 'Error: Arguments must be equivalence relation on the same set {0,1,...,N-1}.'
        return false
    for i in range(N):
        for j in range(N):
            for k in range(N):
                if (are_related(p,i,j) and are_related(q,j,k) and not [i,k] in comp):
                    comp.append([i,k])
    return comp;


# given a partition p, return true if i and j are in the same block of p
def are_related(p, i, j):
    for bloc in p:
        if (i in bloc and j in bloc):
            return true
    return false

# given a binary relation r, return true if r is transitive
def is_transitive(r):
    N = max(max(r))+1
    for i in range(N):
        for j in range(N):
            for k in range(N):
                if ([i,j] in r and [j,k] in r and not [i,k] in r):
                    return false
    return true

# given a binary relation r, return true if r is symmetric
def is_symmetric(r):
    N = max(max(r))+1
    for i in range(N):
        for j in range(N):
            if [i,j] in r and not [j,i] in r:
                return false
    return true

# given a binary relation r, return true if r is reflexive
def is_reflexive(r):
    N = max(max(r))+1
    for i in range(N):
        if not [i,i] in r:
            return false
    return true

# def are_n_permuting(p,q,n):
#     comp_pq = compose(p,q,n)
#     comp_qp = compose(q,p,n)
#     if not len(comp_pq)==len(comp_qp):
#         return false
#     if 
