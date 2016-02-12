def find_upper_intervals(G,i,j,nmin,nmax):
   
    # maximal subgroups
    mscr = G.MaximalSubgroupClassReps()
    #p = Graphics()
    p = []
    indices = []
    for k in [1..len(mscr)]:
 
        # second maximal subgroups
        smscr=mscr[k].MaximalSubgroupClassReps()
        for m in [1..len(smscr)]:
            H = smscr[m]

            # Check that H is core-free.
            corefree=true # First, assume it is.

            if H.Order()>1:
                if G.IsNormal(H):  # first check if H is normal in G 
                    corefree=false # (probably faster than computing the exact core)
                else:
                    core = G.Core(H); # compute core of H in G
                    if core.Order()>1:
                        corefree=false
                    
            if corefree:
                interval_rec = G.IntermediateSubgroups(H)
                intSubgroups = gap.get_record_element(interval_rec, 'subgroups')
                intCoverings = gap.get_record_element(interval_rec, 'inclusions')
                latsize = len(intSubgroups)+2  # intSubgroups doesn't include H and G

                if nmin <= latsize and latsize <= nmax:
                    minx = 0  # minx = min(min(intCoverings)) is always 0
                    maxx = max(max(intCoverings))
                    L = Poset([[minx..maxx],intCoverings.AsList().sage()])
                    # print("Order " + str(latsize))
                    p.append(L.plot(label_elements=False))
                    indices.append([i,j,k,m])

    if len(p)>0:
        G = graphics_array(p)
        G.show(axes=False)
        print indices
    
    return(indices)


