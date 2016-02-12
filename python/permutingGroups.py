import sys

def compose(H,K,n):
    if (n<1):
        sys.exit('Third argument must be a positive integer.')
    if (n==1):
        return H
    return complex_product(H, compose(K, H, n-1))

def complex_product(H,K):
    prodHK=[]
    Hlist=gap.Elements(H)
    Klist=gap.Elements(K)
    for h in Hlist:
        for k in Klist:
            if not h*k in prodHK:
                prodHK.append(h*k)
    return prodHK

# There is a bug in the following routine.
# It's producing true when it should be false.
def are_permuting(H,K,n):
    # returns true if compose(H,K,n)==compose(K,H,n), false otherwise.
    HKH=compose(H,K,n)
    KHK=compose(K,H,n)
    for g in HKH:
        if not g in KHK:
            return false
    for g in KHK:
        if not g in HKH:
            return false
    return true

def normalizes(H, K):
    # returns true if H normalizes K, false otherwise.
    G=gap.ClosureGroup(H, K)
    N=G.Normalizer(K)
    return N.IsSubgroup(H)

