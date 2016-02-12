r"""
Search for upper interval sublattices of subgroup lattices of finite groups.

DESCRIPTION: Mainly a sage wrapper for GAP code which searches for upper 
             intervals in subgroup lattices of primitive groups.  
             (Based on the GAP program findUpperIntervals.g.)

NOTES: This program requires the GAP library of primitive groups.

AUTHORS:

- William DeMeo (2012-12-03): initial version

"""

#*****************************************************************************
#       Copyright (C) 2010 YOUR NAME <your email>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#  as published by the Free Software Foundation; either version 2 of
#  the License, or (at your option) any later version.
#                  http://www.gnu.org/licenses/
#*****************************************************************************


def is_core_free(G, H, cores):
    r"""
    For the given groups 1 < H < G, test whether H is core-free in G.
    
    INPUT:
           G      a group
           H      a subgroup of G
           cores  a (possibly empty) list of normal subgroups of G (cores is merely for speedup)
           
    OUTPUT: 
           corefree   =true if H is corefree in G (false otherwise)
           cores      an (augmented) list of normal subgroups of G

    Author: williamdemeo@gmail.com
    Updated: 2012.12.03
    """
    # corefree=true;  # start by assuming it's core-free
    # if nargin < 3 then cores:=[]; else cores:=args[3]; fi;
    # if nargin < 2 then Error("usage: IsCorefree([G, H, ...]);"); fi;
    # G:=args[1];  H:=args[2];
    # if Order(H) = 1 then Error("usage: IsCorefree([G, H, ...]); with H a NONTRIVIAL subgroup of G"); fi;
    # # The list cores can contain any known normal subgroups of G, in which case the following 
    # # bit of code may help us to more quickly detect a non-corefree subgroup:
    # if IsBound(cores) then
    #     for N in cores do
    #         if IsSubgroup(H,N) then
    #             corefree:=false;
    #             break;
    #         fi;
    #     od;
    # fi;
    # # If the foregoing quick test didn't find a normal subgroup 
    # # of G inside H, we then check the core of H more carefully.
    # if corefree=true then
    #     if IsNormal(G,H) then
    #         # checking normality should be faster than computing the core exactly
    #         corefree:=false;  
    #         if IsBound(cores) then Add(cores,H);
    #         else cores:=[H]; fi;
    #         # but if that doesn't do it, we finally use GAP's Core function:
    #     else        
    #         coreH := Core(G,H);
    #         if Order(coreH)>1 then
    #             corefree:=false;
    #             if IsBound(cores) then Add(cores,coreH);
    #             else cores:=[coreH]; fi;
    #         fi;
    #     fi;
    # fi;
    # return [corefree, cores];


def is_isomorphic_interval(list1, list2)
    # Test whether two sets of covering relations are the same modulo relabelling. 
    # This routine works, and accurately identifies matches, but is very slow and/or
    # causes an out-of-memory error when the maximum number in the list of covering 
    # relations is 11 or higher.
    #     local n, m, j, list3, G, p;
    #     if not IsList(list1) or not IsList(list2) then
    #         Error("usage: isIsomorphicInterval( <lst1>, <lst2> );");
    #     fi;
    #     if Length(list1) <> Length(list2)  then
    #         return false;
    #     fi;
    #     list1 := SSortedList(list1);
    #     list2 := SSortedList(list2);
    #     n:=Length(list1);
    #     m:=Maximum(Maximum(list1));
    #     G:=SymmetricGroup(m);
    #     for p in Elements(G) do
    #         list3 := [[ ]];
    #         for j in [1..n] do
    #             list3[j]:=List(list1[j], x->((x+1)^p)-1); 
    #         od;
    #         list3:=SSortedList(list3);
    #         if list3=list2 then
    #             return true;
    #         fi;
    #     od;
    #     return false;
    # end;

def find_upper_intervals(n1, n2, minsz, maxsz)
    # Search among groups of order n1 <= |G| <=n2, and output all (isomorphism classes of) 
    # upper interval lattices L=[H,G] with minsz <= |L| <= maxsz.
    #
    # Inputs: n1,n2       search among groups G of order n1 <= |G| <= n2.
    #         minsz       ignore intervals with less than minsz elements
    #         maxsz       ignore intervals with more than maxsz elements
    # Output: file        The output file is called something like find_upper_intervals-n1-n2.out 
    #                     (Other strings may be added to the file name depending on what arguments are used
    #                     when the function is called.)  The file stores the non-isomorphic upper interval 
    #                     lattices L=[H,G] with minsz <= |L| <= maxsz among groups of order n1 <= |G| <=n2. 
    #
    # Example: findUpperIntervals( [ 3, 255, 4, 10] );
    #          # finds all upper intervals [H, G] of groups of orders 
    #          # 2 < |G| < 256 such that H is core free and such that the 
    #          # interval [H, G] contains at least 4 and at most 10 elements.
    #
    # Author: <williamdemeo@gmail.com>
    # updated: 2012.12.03
    #

    newcnt=0;  maxsize=0; ncfcnt=0;
    
    pgroups=0;  # don't check p-groups
    abelian=0;  # don't check abelian groups
    solvable=0;  # don't check solvable groups
    # We could check three conditions at once by choosing an appropriate ONanScottType.

    prefix = "find_upper_intervals"
    # This one stores output in human readable format:
    filename = prefix + "-" + str(n1) + "-" + str(n2)
    outfile = file(filename + ".out", 'w')
    logfile = file(filename + ".log", 'w')
    
    lats =  [[[]]]  # stores lattices we have found 
    # lats[j] is a list of lists of lists e.g.
    # lats[5] = [ [ [0,1],[0,2],[1,3],[2,4],[3,4] ], [ [0,1],[0,2],[0,3],[1,4],[2,4],[3,4] ] ]
    # indicates that we have found two 5-element lattices (N5 and M3).
    
    for i in [n1..n2]:
        numpg=gap.NrPrimitiveGroups(i)
        
        print("Checking the " + str(numpg) + " primitive group(s) of degree " + str(i) + "...")
        #  (so far ", newcnt, " intervals, ", ncfcnt, " non-corefree) \n");
        logfile.write("checking " + str(numsg) + "prim group(s) of degree " + str(i) + "...")
        
        for j in [1..numpg]:
            G = gap.PrimitiveGroup(i,j)
            cores=[]   # Clear list of cores from the previous group!
            lats=[[]]  # Clear list of lattices found in previous group (we may want to comment this out)
            
            # Step 1: check if we want to include this group in the search.
            ignore=false   # Begin by assuming we don't want to ignore this group.

            # p-groups
            if pgroup==0:
                print("Checking if it's a p-group")
                if G.IsPGroup():
                    ignore=true

            # abelian groups
            if not ignore:
                if abelian==0:
                    print("Checking if it's abelian.")
                    if G.IsAbelian():
                        ignore=true
            
            # solvable groups
            if not ignore:
                if solvable==0:
                    print("Checking if it's solvable.")
                    if G.IsSolvable():
                        ignore=true
            
            if not ignore:
                
                # H=gap.Stabilizer(G,1) (we don't look above stabilizer for primitive groups
                #   like we did for trans groups -- else we would just get the two element lattice.)
           
                obtained=false   # indicator (have we seen this lattice already?)

                mscr = G.MaximalSubgroupClassReps()

                for k in [1..len(mscr)]:

                    # Find the second maximal subgroups of G
                    smscr = mscr[k].MaximalSubgroupClassReps()

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

                            if minsz <= latsize and latsize <= maxsz:
                                incls = SSortedList(intSubs.inclusions);
                            if norepeats<>1 then
                                newcnt:=newcnt+1;
                            else
                                if len(lats[0])>0 then
                                    # check if we're already seen [H, G]
                                    if incls in lats[latsize] then
                                        obtained:=true;
                                    elif norepeats=1 then # really check carefully
                                        for t in [1..Size(lats[latsize])] do
                                            if isIsomorphicInterval(lats[latsize][t], incls) then
                                                obtained:=true;
                                                break;
                                            fi;
                                        od;
                                    fi;
                                    if not obtained then
                                        # add this lattice to the list of representable lattices
                                        Add(lats[latsize], incls);
                                        newcnt:=newcnt+1;
                                    fi;
                                else  # (we haven't seen any intervals of this size yet)
                                    lats[latsize]:=[incls];
                                    newcnt:=newcnt+1;
                                fi;
                            fi;
                            if not obtained then
                                AppendTo(outfile, "\n", newcnt, ".(", latsize, ")  G = TransitiveGroup(", i, ", ", j, ")");
                                AppendTo(datfile, incls,"; (",latsize, ")  [H,G] = [Stab(1), TransitiveGroup(", i, ",", j, ")]; ");
                                if VERBOSE>0 then
                                    # strucG:=UnderControlTime(StructureDescription, [G], maxtime);
                                    # strucH:=UnderControlTime(StructureDescription, [H], maxtime);
                                    strucG:=StructureDescription(G);
                                    strucH:=StructureDescription(H);
                                    AppendTo(outfile, " = ", strucG, " H = Stab(1) = ", strucH);
                                    AppendTo(datfile, " [ ", strucH, ",  ", strucG, " ]; ");
                                    if latsize < 12 then
                                        AppendTo(datfile, List(intSubs.subgroups, x->Index(G,x)), " ");
                                        if VERBOSE>1 then
                                            AppendTo(datfile, List(intSubs.subgroups, x->StructureDescription(x)));
                                        fi;
                                    fi;
                                else
                                    AppendTo(datfile, ";  ");
                                fi;
                                AppendTo(outfile, ",  ", incls, "\n"); 
                                AppendTo(datfile, "\n");
                            fi;
                        fi;
                    fi;                    
                    
                    # ======= Small Groups =======
                else
                    # e := Group([Identity(G)]);
                    cc := ConjugacyClassesSubgroups(G);
                    numcc := Size(cc);
                    
                    first:=2;  # I THINK the penultimate conjugacy class rep is always a maximal subgroup
                    # but we check this with the following test code, just to be sure:
                    if BETA then
                        H:= Representative(cc[numcc-1]);
                        intSubs:=IntermediateSubgroups(G, H);
                        if intSubs.subgroups<>[] then
                            Print("\nTEST FAILED: penultimate conjugacy class is not a maximal subgroup\n");
                            Print("G = SmallGroup(", i, ", ", j, ")  H = CC[", numcc-1, "] \n");                       
                            AppendTo(logfile, "\nTEST FAILED: penultimate conjugacy class is not a maximal subgroup\n");
                            AppendTo(logfile, "G = SmallGroup(", i, ", ", j, ")  H = CC[", numcc-1, "] \n");
                        fi;
                    fi;
                    
                    # It makes more sense to start with the last conjugacy class and work down, 
                    # so that you can record the interval of minimal index for the given group.
                    for k in [first..(numcc-1)] do
                        H:= Representative(cc[numcc-k]);
                        obtained:=false;   # indicator (have we seen this lattice already?)
                        
                        # Check that H is core-free.
                        corefree:=true; # First, assume it is.
                        if core=0 and Order(H)>1 then
                            answer:=IsCorefree([G,H,cores]);
                            corefree:=answer[1];
                            cores:=answer[2];
                        fi;
                        if not corefree then
                            ncfcnt:=ncfcnt+1;
                        else
                            intSubs := IntermediateSubgroups(G, H);
                            latsize := Size(intSubs.subgroups)+2;
                            if minsz <= latsize and latsize <= maxsz then
                                incls := SSortedList(intSubs.inclusions);
                                if norepeats=-1 then
                                    newcnt:=newcnt+1;
                                else
                                    if IsBound(lats[latsize]) then
                                        # check if we're already seen [H, G]
                                        if incls in lats[latsize] then
                                            obtained:=true;
                                        elif norepeats=1 then # really check carefully
                                            for t in [1..Size(lats[latsize])] do
                                                if isIsomorphicInterval(lats[latsize][t], incls) then
                                                    obtained:=true;
                                                    break;
                                                fi;
                                            od;
                                        fi;
                                        if not obtained then
                                            # add this lattice to the list of representable lattices
                                            Add(lats[latsize], incls);
                                            newcnt:=newcnt+1;
                                        fi;
                                    else  # (we haven't seen any intervals of this size yet)
                                        lats[latsize]:=[incls];
                                        newcnt:=newcnt+1;
                                    fi;
                                fi;
                                if not obtained then
                                    indx:=Index(G,H);
                                    AppendTo(outfile, "\n", newcnt, ".(", latsize, ")  G = SmallGroup(", i, ", ", j, ")");
                                    if VERBOSE>0 then
                                        AppendTo(outfile, " = ", StructureDescription(G), " H = CC[", numcc-k, "] = ", StructureDescription(H));
                                    fi;
                                    AppendTo(outfile, "  Index: ", indx, ", ",  incls, "\n"); 
                                    
                                    AppendTo(datfile, incls,"; (",latsize, ")  [H,G] = [CC[",numcc-k,"], SmallGroup(", i, ",", j, ")], Index ", indx, "; ");
                                    if i < 128 or VERBOSE>0 then
                                        AppendTo(datfile, " [ ", StructureDescription(H), ",  ", StructureDescription(G), " ]; ");
                                        if latsize < 12 then
                                            AppendTo(datfile, List(intSubs.subgroups, x->Index(G,x)), " ");
                                            if i < 128 or VERBOSE>1 then
                                                AppendTo(datfile, List(intSubs.subgroups, x->StructureDescription(x)));
                                            fi;
                                        fi;
                                    else
                                        AppendTo(datfile, ";  ");
                                    fi;
                                    AppendTo(datfile, "\n");
                                fi;
                            fi;
                        fi;
                    od;
                fi;
            fi;
        od;
    od;
end;;



findUpperIntervalsBeta:=function(args)
    # findUpperIntervalsBeta:=function([n1, n2, minsz, maxsz, abelian, solvable, core])
    # GAP function which searches among all groups of order n1 <= |G| <=n2, and outputs all
    # (isomorphism classes of) upper interval lattices L=[H,G] with minsz <= |L| <= maxsz.
    #
    # Inputs: n1,n2       search among groups G of order n1 <= |G| <= n2.
    #         minsz       ignore intervals with less than minsz elements
    #         maxsz       ignore intervals with more than maxsz elements
    #         abelian     (optional,default=1) if 0, don't include abelian groups in the search. 
    #         solvable    (optional,default=1) if 0, don't include solvable groups in the search.
    #         core        (optional,default=0) if 0, don't include intervals [H,G] when H is not core-free. 
    #
    # Output: file        The output file is called output/findUpperIntervalsN.out where N=n.
    #                     It stores the non-isomorphic upper interval lattices L = [H, G], 
    #                     with minsz <= |L| <= maxsz, among all groups of order n1 <= |G| <=n2. 
    #
    # Differences in the Beta version:
    # Maintains a list of non-trivial cores below conjugacy class reps.  
    # Instead of always computing core of H, first checks whether a previously computed 
    # core is below H.
    #
    # Author: <williamdemeo@gmail.com>
    # Date: 2011.02.24
    #
    local i, j, k, m, r, s, pathname, filename, datfile, outfile, first, incls, newcnt, maxsize, indx,
          G, e, cc, numcc, numsg, lats, latsize, obtained, intSubs, H, perm, t, corefree, minnormals, cores,
          n1, n2, minsz, maxsz, abelian, solvable, core, nargin, N, prefix, coreH;
    
    pathname := getPathName();
    
    nargin := Length(args);
    if nargin < 7 then core:=0; else core:=args[7]; fi;
    if nargin < 6 then solvable:=1; else solvable:=args[6]; fi;
    if nargin < 5 then abelian:=1; else abelian:=args[5]; fi;
    if nargin < 4 then Error("usage: findUpperIntervals([n1, n2, minsize, maxsize, ...]);"); fi;
    n1:=args[1];  n2:=args[2];  minsz:=args[3];  maxsz:=args[4];
    newcnt:=0;  maxsize:=0;
    
    prefix := "UpperIntervalsBeta";
    if solvable=0 then prefix := Concatenation(prefix, "NonSolvable"); 
    elif abelian=0 then prefix := Concatenation(prefix, "NonAbelian"); fi;
    if core=1 then prefix := Concatenation(prefix, "Core"); fi;
    prefix:=Concatenation(prefix, String(n1), "to", String(n2), "Min", String(minsz), "Max", String(maxsz));
    
    pathname := getPathName();
    # This one stores output in human readable format:
    filename := Concatenation(pathname, prefix, ".out");
    outfile := OutputTextFile(filename, false);
    SetPrintFormattingStatus(outfile, false);   # This prevents automatic indentation and line breaks.
    
    # This one stores output in format that will be read in by BatchCovers2Hasse.m Matlab routine:
    filename := Concatenation(pathname, prefix, ".dat");
    datfile := OutputTextFile(filename, false);
    SetPrintFormattingStatus(datfile, false);   # This prevents automatic indentation and line breaks.
    
    PrintTo(outfile, "Command used: findUpperIntervalsBeta( ", args, " ); \n\n");
    
    first := 2;    # the first conjugacy class to check 
    #    if full=0 then first:=2; fi;  # don't include the full subgroup interval [1, G]
    
    lats :=  [[[]]] ;  # stores lattices we have found 
    # lats[j] is a list of lists of lists e.g.
    # lats[5] = [ [ [0,1],[0,2],[1,3],[2,4],[3,4] ], [ [0,1],[0,2],[0,3],[1,4],[2,4],[3,4] ] ]
    # indicates that we have found two 5-element lattices (N5 and M3).
    
    for i in [n1..n2] do
        numsg := NumberSmallGroups(i);
        Print("Checking the ", numsg, " group(s) of order |G| = ", i, "...  (", newcnt, " intervals so far) \n");
        AppendTo(outfile, "Checking the ", numsg, " group(s) of order |G| = ", i, "...  (", newcnt, " intervals so far) \n");
    
        for j in [1..numsg] do
            G := SmallGroup(i,j);
            cores:=[[]];
            if abelian=0 and IsAbelian(G) then
                # do nothing
            elif solvable=0 and IsSolvable(G) then
                # do nothing
            else
                e := Group([Identity(G)]);
                cc := ConjugacyClassesSubgroups(G);
                numcc := Size(cc);
                     
                for k in [first..numcc] do
                
                    H:= Representative(cc[k]);
                    obtained:=0;   # indicator (have we seen this lattice already?)
                    corefree:=1;
                    
                    # check that H is core-free
                    if core=0 and H<>e then
                        for N in cores do
                            if IsSubgroup(H,N) then
                                corefree:=0;
                                break;
                            fi;
                        od;
                        if corefree=1 then
                            coreH := Core(G,H);
                            if coreH<>e then
                                corefree:=0;
                                Add(cores, coreH);
                            fi;
                        fi;
                    fi;
                    
                    if corefree=1 then
                        intSubs := IntermediateSubgroups(G, H);
                        latsize := Size(intSubs.subgroups)+2;
                        
                        if minsz <= latsize and latsize <= maxsz then
                            incls := SSortedList(intSubs.inclusions);
                        
                            if IsBound(lats[latsize]) then
                        
                                # check if [H, G] is isomorphic to something we've already seen
                                if incls in lats[latsize] then
                                    # do nothing
                                    obtained := 1;
                                else
                                     for t in [1..Size(lats[latsize])] do
                                         if isIsomorphicInterval(lats[latsize][t], incls) then
                                             obtained := 1;
                                             break;
                                         fi;
                                     od;
                                 fi;
                                
                                 if obtained=0 then
                                    # add this lattice to the list of representable lattices
                                     Add(lats[latsize], incls);
                                    newcnt:=newcnt+1;
                                fi;
                            else
                                # add this lattice to the list of representable lattices
                                lats[latsize]:=[incls];
                                newcnt:=newcnt+1;
                            fi;
                            
                            if obtained=0 then
                                indx:=Index(G,H);
                                AppendTo(outfile, "\n", newcnt, ".(", latsize, ")  G = SmallGroup(", i, ", ", j, ");  H = CC[", k, "] "); 
                                AppendTo(outfile, "   Index: ", indx, "\n"); 
                                AppendTo(outfile, "       [H, G] = ",  incls, "\n"); 
                                AppendTo(datfile, incls,"; ");
                                AppendTo(datfile, "G=SmallGroup(", i, ",", j, ");  H=CC[",k,"]  Index ", indx, "\n");
                                maxsize:= Maximum(maxsize, latsize);
                            fi;
                        fi;
                    fi;
                
                od;
            fi;
        od;
    od;
    AppendTo(outfile, "\n\n---------------------------------------------\n\n");
    AppendTo(outfile, "(i, j)     jth Lattice of size i\n\n");
    for r in [1..maxsize] do
        if IsBound(lats[r]) then
            if Size(lats[r])>0 then
                for s in [1..Size(lats[r])] do
                    AppendTo(outfile, "(", r, ",", s, ")   ", lats[r][s], "\n");
                od;
            fi;
        fi;
    od;
end;;

    
# The following two functions were suggested on the GAP forum
# by Bettina Eick <beick@tu-bs.de >, as a means of 
# collecting the minimal normal subgroups of a group.
AddToSubgroupList := function( nt, U )
local i, N;
    # check if U is minimal in nt
    for N in nt do if IsSubgroup(U, N) then return nt; fi; od;
    
    # check that nt remains minimal
    for i in [1..Length(nt)] do
        if IsSubgroup(nt[i], U) then nt[i] := false; fi;
    od;
    nt := Filtered( nt, x -> not IsBool(x) );

    # add U and return
    Add(nt, U); return nt;
end;

minimalNormalSubgroups := function(G)
    local cl, nt, c, U;
    cl := ConjugacyClasses(G);
    nt := [];
    for c in cl do
        if IsPrime(Order(Representative(c))) then
            U  := Subgroup( G, [Representative(c)] );
            U  := NormalClosure( G, U );
            nt := AddToSubgroupList( nt, U );
        fi;
    od;
    return nt;
end;




findM4UpperIntervals:=function(args)
    # findM4UpperIntervals:=function([n1, n2, abelian, solvable, core])
    # GAP function which searches among all groups of order n1 <= |G| <=n2, and outputs all
    # upper intervals that are isomorphic to M_4.
    #
    # Inputs: n1,n2       search among groups G of order n1 <= |G| <= n2.
    #         abelian     (optional,default=1) if 0, don't include abelian groups in the search. 
    #         solvable    (optional,default=1) if 0, don't include solvable groups in the search.
    #         core        (optional,default=0) if 0, don't include intervals [H,G] when H is not core-free. 
    #         method      (optional,default=0) method to use
    #
    # Output: file        The output file is called output/M4UpperIntervalsN1toN2.out where N1=n1, N2=n2.
    #
    # IMPORTANT NOTES
    #        1. change the output path name below from
    #               pathname := "~/pub/DeMeo/research/LatticeTheory/GAP/outputs";
    #           to something more appropriate for you.
    #
    # Example: findM4UpperIntervals( [ 3, 255, 0, 1 ]);
    #          # finds all upper intervals [H, G] of nonabelian groups of orders 
    #          # 2 < |G| < 256 such that H is core free and such that the 
    #          # interval [H, G] is M_4.
    #
    # Author: <williamdemeo@gmail.com>
    # Date: 2011.04.28
    #
    local i, j, k, m, r, s, pathname, filename, datfile, outfile, first, incls, M4cnt, orb, indx, omega, act, 
          blks, cores, G, e, cc, numcc, numsg, intSubs, H, t, prefix, n1, n2, abelian, solvable, core, nargin, 
          flag, method, corefree, answer, coreH;
        
    pathname := getPathName();
    
    nargin := Length(args);
    
    if nargin < 6 then method:=0; else method:=args[6]; fi;
    if nargin < 5 then core:=0; else core:=args[5]; fi;
    if nargin < 4 then solvable:=1; else solvable:=args[4]; fi;
    if nargin < 3 then abelian:=1; else abelian:=args[3]; fi;
    if nargin < 2 then
        Error("usage: findM4UpperIntervals([n1, n2, ...]);");
    fi;
    
    n1:=args[1];  n2:=args[2];  M4cnt:=0;
    
    prefix := "M4UpperIntervalsAlpha";
    if solvable=0 then prefix := Concatenation(prefix, "NonSolvable"); 
    elif abelian=0 then prefix := Concatenation(prefix, "NonAbelian"); fi;
    if core=1 then prefix := Concatenation(prefix, "Core"); fi;
    prefix:=Concatenation(prefix, String(n1), "to", String(n2));
    
    pathname := getPathName();
    # This one stores output in human readable format:
    filename := Concatenation(pathname, prefix, ".out");
    outfile := OutputTextFile(filename, false);
    SetPrintFormattingStatus(outfile, false);   # This prevents automatic indentation and line breaks.
    
    # This one stores output in format that will be read in by BatchCovers2Hasse.m Matlab routine:
    filename := Concatenation(pathname, prefix, ".dat");
    datfile := OutputTextFile(filename, false);
    SetPrintFormattingStatus(datfile, false);   # This prevents automatic indentation and line breaks.
    
    PrintTo(outfile, "Command used: findM4UpperIntervals( ", args, " ); \n\n");
    
    first:=1; # whether to include the full subgroup interval [1, G]  (if not, set first:=2)
    
    for i in [n1..n2] do
        numsg := NumberSmallGroups(i);
        Print("Checking the ", numsg, " group(s) of order |G| = ", i, "...  (", M4cnt, " M4 intervals so far) \n");
        AppendTo(outfile, "Checking the ", numsg, " group(s) of order |G| = ", i, "...  (", M4cnt, " M4 intervals so far) \n");
    
        for j in [1..numsg] do
            G := SmallGroup(i,j);
            
            if method=1 then
                cores:=minimalNormalSubgroups(G);
            else
                cores:=[[]];
            fi;
            
            if abelian=0 and IsAbelian(G) then
                # do nothing
            elif solvable=0 and IsSolvable(G) then
                # do nothing
            else
                #e := Group([Identity(G)]);
                cc := ConjugacyClassesSubgroups(G);
                numcc := Size(cc);
                     
                for k in [first..numcc-1] do
                
                    H:= Representative(cc[k]);
                    
                    corefree:=true;
                    #                    if core=0 and H<>e then   
                    if core=0 and Order(H)>1 then   
                        # check whether H is core-free
                        if method=2 then
                            if IsNormal(G,H) then
                                corefree:=false;
                            else
                                coreH := Core(G,H);
                                if Order(coreH)>1 then
                                    corefree:=false;
                                fi;
                            fi;
                        else
                            answer:=IsCorefree([G,H,cores]);
                            corefree:=answer[1];
                            cores:=answer[2];
                        fi;
                    fi;
                    if corefree then
                        intSubs := IntermediateSubgroups(G, H);
                        if Size(intSubs.subgroups)=4 then
                            incls := intSubs.inclusions;
                            flag:=1;
                            for m in [1..4] do
                                if not ([0, m] in incls) then
                                    flag:=0;  # not an M_4
                                    break;
                                fi;
                            od;
                            if flag=1 then
                                M4cnt:=M4cnt+1;
                                indx:=Index(G,H);
                                AppendTo(outfile, "\n", M4cnt, ".  G = SmallGroup(", i, ", ", j, ")  H = CC[", k, "] "); 
                                AppendTo(outfile, "   Index: ", indx, "\n"); 
                                AppendTo(outfile, "       [H, G] = ",  incls, "\n"); 
                                AppendTo(datfile, incls,"; ");
                                AppendTo(datfile, "[CC[",k,"], SmallGroup(", i, ",", j, ")];   Index ", indx, "\n");
                                omega:=RightCosets(G,H);
                                act:=Action(G, omega, OnRight);
                                blks:=AllBlocks(act);
                                if Size(blks) <> 4 then
                                    Error("wrong number of blocks!!");
                                fi;
                                for m in [1..4] do
                                    orb:=Orbit(act,blks[m],OnSets)-1;
                                    AppendTo(datfile, "gam", m, "=");
                                    for r in [1..Size(orb)] do
                                        AppendTo(datfile, orb[r]);
                                    od;
                                    AppendTo(datfile, "\n");
                                od;
                                AppendTo(datfile, "\n");
                            fi;
                        fi;
                    fi;
                od;
            fi;
        od;
    od;
end;;


findUpperIntervalsInG:=function(args)
    # findUpperIntervalsInG:=function([G, minsz, maxsz, core, datfile, i, j])
    # Search the given group G for upper intervals L=[H,G] such that minsz <= |L| <= maxsz.
    #
    # Inputs: G           the given group
    #         minsz       ignore intervals with less than minsz elements
    #         maxsz       ignore intervals with more than maxsz elements
    #         core        (optional,default=0) if 0, don't include intervals [H,G] when H is not core-free. 
    #
    # Output: lats        a list of lists of covering relations
    #
    # Author: <williamdemeo@gmail.com>
    # Date: 2011.05.05
    #
    local i, j, k, h, m, r, s, first, incls, newcnt, maxsize, indx, 
          G, K, H, cc, numcc, numsg, lats, latsize, obtained, intSubs, perm, t, corefree, minnormals,
          minsz, maxsz, core, nargin, N, ms, sms, datfile;
        
    nargin := Length(args);
    if nargin < 5 then 
        datfile:=0; i:=0; j:=0;
    elif nargin < 7 then 
        # (if you have more than 4 input arguments, you must have 7)
        Error("usage: findUpperIntervalsInG([G, minsz, maxsz, core, datfile, i, j]);"); 
    else
        datfile:=args[5]; i:=args[6];  j:=args[7];
    fi;
    if nargin < 4 then core:=0; else core:=args[4]; fi;
    if nargin < 3 then Error("usage: findUpperIntervalsInG([G, minsz, maxsz, ...]);"); fi;
    G:=args[1];  minsz:=args[2];  maxsz:=args[3];  
    newcnt:=0;      
    lats :=  [[[]]] ;  # stores lattices we have found 
    # lats[j] is a list of lists of lists e.g. lats[5] = [ [ [0,1],[0,2],[1,3],[2,4],[3,4] ], [ [0,1],[0,2],[0,3],[1,4],[2,4],[3,4] ] ]
    # indicates that we have found two 5-element lattices (N5 and M3).
    
    if core=0 then minnormals:=minimalNormalSubgroups(G); fi;
    
    ms:=MaximalSubgroupClassReps(G);
#    Print("Checking the ", Length(ms), " maximal subgroup class reps of G\n");
#    Print("They have ", List(ms, x->Length(MaximalSubgroupClassReps(x))), " maximal subgroups, respectively\n");
    for k in [1..Size(ms)] do
        K:=ms[k];
        sms:=MaximalSubgroupClassReps(K);
        for h in [1..Size(sms)] do
            H:=sms[h];
            obtained:=0;   # indicator (have we seen this lattice already?)
            corefree:=true;
            if core=0 and Order(H)>1 then
                # check that H is core-free
                for N in minnormals do
                    if IsSubgroup(H,N) then
                        corefree:=false;
                        break;
                    fi;
                od;
            fi;
            
            if corefree then
                intSubs := IntermediateSubgroups(G, H);
                latsize := Size(intSubs.subgroups)+2;
                if minsz <= latsize and latsize <= maxsz then
                    incls := SSortedList(intSubs.inclusions);
                    if IsBound(lats[latsize]) then
                        # check if [H, G] is isomorphic to something we've already seen
                        if incls in lats[latsize] then
                            # do nothing
                            obtained := 1;
                        else
                            for t in [1..Size(lats[latsize])] do
                                if isIsomorphicInterval(lats[latsize][t], incls) then
                                    obtained := 1;
                                    break;
                                fi;
                            od;
                        fi;
                        if obtained=0 then
                            # add this lattice to the list of representable lattices
                            Add(lats[latsize], incls);
                            newcnt:=newcnt+1;
                            if datfile<>0 then
                                AppendTo(datfile,  incls, ";  (", latsize, ") SmallGroup(",i,",",j,");  (",k,",",h,") Index:", Index(G,H),"\n");
                            fi;
                        fi;
                    else
                        # add this lattice to the list of representable lattices
                        lats[latsize]:=[incls];
                        newcnt:=newcnt+1;
                        if datfile<>0 then
                            AppendTo(datfile,  incls, ";  (", latsize, ") SmallGroup(",i,",",j,");  (",k,",",h,") Index:", Index(G,H),"\n");
                        fi;
                    fi;
                fi;
            fi;
        od;
    od;
    return lats;
end;


findUpperIntervalsAlpha:=function(args)
    # findUpperIntervalsAlpha:=function([n1, n2, minsz, maxsz, abelian, solvable, core,norepeats])
    # Search among groups of order n1 <= |G| <=n2, and output all (isomorphism classes of) upper 
    # intervals L=[H,G] with minsz <= |L| <= maxsz.
    #
    # Inputs: n1,n2       search among groups G of order n1 <= |G| <= n2.
    #         minsz       ignore intervals with less than minsz elements
    #         maxsz       ignore intervals with more than maxsz elements
    #         abelian     (optional,default=1) if 0, don't include abelian groups in the search. 
    #         solvable    (optional,default=1) if 0, don't include solvable groups in the search.
    #         core        (optional,default=0) if 0, don't include intervals [H,G] when H is not core-free. 
    #         norepeats   (optional,default=0) if 0, include lattices, even if we've seen them in other groups.
    #
    # Output: file        The output file is called output/findUpperIntervalsN.out where N=n.
    #                     It stores the non-isomorphic upper interval lattices L = [H, G], 
    #                     with minsz <= |L| <= maxsz, among all groups of order n1 <= |G| <=n2. 
    #
    # Notes: This version is more modular in that it calls the findUpperIntervalsInG to do the work.
    #        It's better in that it's more modular, but worse because it doesn't keep track of the 
    #        index [G:H] for each upper interval found, nor the exact specification of the subgroup H in G.
    #
    # Author: <williamdemeo@gmail.com>
    # Date: 2011.02.24
    #
    local i, j, k, m, r, s, pathname, filename, datfile, outfile, first, incls, newcnt,
          G, e, numsg, lats, latsize, obtained, intSubs, t, corefree, minnormals, L,
          n1, n2, minsz, maxsz, abelian, solvable, core, nargin, N, prefix, norepeats;
    
    nargin := Length(args);
    
    if nargin < 8 then norepeats:=0; else norepeats:=args[8]; fi;
    if nargin < 7 then core:=0; else core:=args[7]; fi;
    if nargin < 6 then solvable:=1; else solvable:=args[6]; fi;
    if nargin < 5 then abelian:=1; else abelian:=args[5]; fi;
    if nargin < 4 then Error("usage: findUpperIntervals([n1, n2, minsize, maxsize, ...]);"); fi;
    
    n1:=args[1];  n2:=args[2];  minsz:=args[3];  maxsz:=args[4];
    newcnt:=0;
    
    prefix := "UpperIntervalsAlpha";
    if solvable=0 then prefix := Concatenation(prefix, "NonSolvable"); 
    elif abelian=0 then prefix := Concatenation(prefix, "NonAbelian"); fi;
    if core=1 then prefix := Concatenation(prefix, "Core"); fi;
    prefix:=Concatenation(prefix, String(n1), "to", String(n2), "Min", String(minsz), "Max", String(maxsz));
    
    pathname := getPathName();
    # This one stores output in human readable format:
    filename := Concatenation(pathname, prefix, ".out");
    outfile := OutputTextFile(filename, false);
    SetPrintFormattingStatus(outfile, false);   # This prevents automatic indentation and line breaks.
    # This one stores output in format that will be read in by BatchCovers2Hasse.m Matlab routine:
    filename := Concatenation(pathname, prefix, ".dat");
    datfile := OutputTextFile(filename, false);
    SetPrintFormattingStatus(datfile, false);   # This prevents automatic indentation and line breaks.
    PrintTo(outfile, "Command used: findUpperIntervalsAlpha( ", args, " ); \n\n");
    
    first := 2;    # the first conjugacy class to check 
    lats :=  [[[]]] ;  # stores lattices we have found 
    for i in [n1..n2] do
        numsg := NumberSmallGroups(i);
        Print("Checking the ", numsg, " group(s) of order |G| = ", i, "...  (", newcnt, " intervals so far) \n");
        AppendTo(outfile, "Checking the ", numsg, " group(s) of order |G| = ", i, "...  (", newcnt, " intervals so far) \n");
        
        for j in [1..numsg] do
            G := SmallGroup(i,j);
            if abelian=0 and IsAbelian(G) then   # do nothing
            elif solvable=0 and IsSolvable(G) then  # do nothing
            else
                incls:=findUpperIntervalsInG([G, minsz, maxsz, core]);
                for k in [1..Length(incls)] do
                    if IsBound(incls[k]) then
                        for L in incls[k] do
                            if L<>[ ] then
                                obtained:=0;
                                if norepeats=1 then
                                    if IsBound(lats[k]) then
                                        # check if [H, G] is isomorphic to something we've already seen
                                        if L in lats[k] then
                                            # do nothing
                                            obtained := 1;
                                        else
                                            for t in [1..Size(lats[k])] do
                                                if isIsomorphicInterval(lats[k][t], L) then
                                                    obtained := 1;
                                                    break;
                                                fi;
                                            od;
                                        fi;
                                        if obtained=0 then
                                            # add this lattice to the list of representable lattices
                                            Add(lats[k], L);
                                            newcnt:=newcnt+1;
                                        fi;
                                    else
                                        # add this lattice to the list of representable lattices
                                        lats[k]:=[L];
                                        newcnt:=newcnt+1;
                                    fi;
                                else
                                    newcnt:=newcnt+1;
                                fi;
                                if obtained=0 then
                                    AppendTo(outfile, "\n", newcnt, ".(", k, ")  G = SmallGroup(", i, ", ", j, ") "); 
                                    AppendTo(outfile, "       [H, G] = ",  L, "\n"); 
                                    AppendTo(datfile, L,"; ");
                                    AppendTo(datfile, "G=SmallGroup(", i, ",", j, ");\n");
                                fi;
                            fi;
                        od;
                    fi;
                od;
            fi;
        od;
    od;
end;;


findUpperIntervalsInAltSymAlpha:=function(args)
    # findUpperIntervalsInAltSym:=function([n1, n2, minsz, maxsz, AltSym])
    # GAP function which searches among all alternating (symmetric) groups A_n (S_n) with n1 <= n <=n2
    # outputs all (isomorphism classes of) upper interval lattices L = [H, A_n] or L = [H, S_n] 
    # such that minsz <= |L| <= maxsz.
    #
    # Inputs: n1,n2       search among groups A_n with n1 <= n <= n2.
    #         minsz       ignore intervals with less than minsz elements
    #         maxsz       ignore intervals with more than maxsz elements
    #         AltSym      (optional,default=1) if 0, check alternating group, else check symmetric group.
    #
    # Output: file        The output file is called output/UpperIntervalsAn____.out
    #                     It stores the non-isomorphic upper interval lattices L=[H,A_n] with 
    #                     minsz <= |L| <= maxsz.
    #
    # IMPORTANT NOTES
    #        1. change the output path name below from
    #               pathname := "~/pub/DeMeo/research/LatticeTheory/GAP/outputs";
    #           to something more appropriate for you.
    #
    # Example: findUpperIntervalsInAltSym([3, 7, 7, 10]);
    #          # finds all upper intervals L=[H, S_n] in Sub[S_n] for 2 < n < 8 and 6 < |L| < 11. 
    #
    # Author: <williamdemeo@gmail.com>
    # Date: 2011.04.17
    #
    local i, j, k, m, r, s, pathname, filename, datfile, outfile, incls, newcnt, indx, prefix, L, K,
          G, e, cc, numcc, numsg, lats, latsize, obtained, intSubs, H, perm, t, maxdepth, maxindex, minindex,
          n1, n2, minsz, maxsz, abelian, solvable, core, nargin, checkiso, AltSym, AS;
    
    
    pathname:= getPathName();
    
    nargin := Length(args);
    if nargin < 5 then AltSym:=1; else AltSym:=args[5]; fi;
    if nargin < 4 then Error("usage: findUpperIntervalsInAn([n1, n2, minsize, maxsize]);"); fi;
    n1:=args[1];  n2:=args[2];  minsz:=args[3];  maxsz:=args[4];  newcnt:=0;
    
    if AltSym=0 then AS := "A"; else AS := "S"; fi;
    
    prefix:=Concatenation(pathname, "UpperIntervalsIn", AS, String(n1), "to", AS, String(n2), 
                    "Min", String(minsz), "Max", String(maxsz), "NEW");
        
    filename := Concatenation(prefix, ".out");
    outfile := OutputTextFile(filename, false);
    SetPrintFormattingStatus(outfile, false);   # This prevents automatic indentation and line breaks.
    
    PrintTo(outfile, "Command used: findUpperIntervalsInAltSymAlpha( ", args, " ); \n\n");

    lats :=  [[[]]] ;  # stores lattices we have found 
    # lats[j] is a list of lists of lists e.g. lats[5] = [ [ [0,1],[0,2],[1,3],[2,4],[3,4] ], [ [0,1],[0,2],[0,3],[1,4],[2,4],[3,4] ] ]
    # indicates that we have found two 5-element lattices (N5 and M3).
    newcnt:=0;
    
    for i in [n1..n2] do
        Print("Checking the group G = ", AS, i, "...  (", newcnt, " intervals so far) \n");
        AppendTo(outfile,"Checking the group G = ", AS, i, "...  (", newcnt, " intervals so far) \n");
        if AltSym=0 then 
            G := AlternatingGroup(i);
        else 
            G := SymmetricGroup(i); 
        fi;
        
        cc:=ConjugacyClassesSubgroups(G);
        numcc:=Size(cc);
        
        maxdepth:=Int(numcc/2)+1;
        
        for j in [1..maxdepth] do
            K:= Representative(cc[numcc-j]);
            if IsSolvable(K) then
                # do nothing
            else
                incls:=findUpperIntervalsInG([K, minsz, maxsz, 0, 2]);
                
                for k in [1..Length(incls)] do
            
                    if IsBound(incls[k]) then
                        for L in incls[k] do
                            obtained:=0;
                            if IsBound(lats[k]) then
                            
                                # check if [H, G] is isomorphic to something we've already seen
                                if L in lats[k] then
                                    # do nothing
                                    obtained := 1;
                                else
                                    for t in [1..Size(lats[k])] do
                                        if isIsomorphicInterval(lats[k][t], L) then
                                            obtained := 1;
                                            break;
                                        fi;
                                    od;
                                fi;
                                
                                if obtained=0 then
                                    # add this lattice to the list of representable lattices
                                    Add(lats[k], L);
                                    newcnt:=newcnt+1;
                                fi;
                            else
                                # add this lattice to the list of representable lattices
                                lats[k]:=[L];
                                newcnt:=newcnt+1;
                            fi;
                        
                            if obtained=0 then
                                Print("(", k, ")", L, "   CC[", numcc-j, "]=", StructureDescription(K),"; \n"); 
                                AppendTo(outfile, L, "; (", k, ")  CC[", numcc-j, "]=", StructureDescription(K),"; \n"); 
                            fi;
                        od;
                    fi;
                od;
            fi;
        od;
    od;
end;;


printUpperIntervalsInG:=function(args)
    # printUpperIntervalsInG:=function([G, datfile, i, j, TYPE, minL, maxL])
    # Find upper intervals, with at least (most) minL (maxL) elements, above second maximal subgroups of G.
    # 
    local K, H, ms, msK, h, i, j, k, intHG, numms, nameG, pathname, filename, G,
          outfile, nargin, verbose, latsize, core, corefree, coreH, prim, TYPE,
          minL, maxL;
    verbose:=0; core:=0;
    G:=args[1];
    nargin := Length(args);
    if nargin < 7 then maxL:=0; else maxL:=args[7]; fi;
    if nargin < 6 then minL:=0; else minL:=args[6]; fi;
    if nargin < 5 then TYPE:="Small"; else TYPE:=args[5]; fi;  # the default is to print "SmallGroups(i,j)". If prim=1, print PrimitiveGroup(i,j).
    if nargin < 4 then j:=0; else j:=args[4]; fi;
    if nargin < 3 then i:=0; else i:=args[3]; fi;
    if nargin < 2 then 
        verbose:=1;
        nameG:=StructureDescription(G);
        pathname := getPathName();
        filename:=Concatenation(pathname, "SecondMaximalUpperIntervalsIn", nameG, ".dat");
        outfile := OutputTextFile(filename, false);
        SetPrintFormattingStatus(outfile, false);   # This prevents automatic indentation and line breaks.
        PrintTo(outfile, "Command used: PrintUpperIntervalsInG( ", args, " ); \n\n");
    else
        outfile:=args[2];
    fi;
    ms:=MaximalSubgroupClassReps(G);
    numms:=Size(ms);
    if verbose=1 then
        Print("\n==== Checking the ", numms, " maximal subgroups of ", nameG, " ====\n");
#        AppendTo(outfile,"\n==== Checking the ", numms, " maximal subgroups of ", nameG, " ====\n");
    fi;
    
    for k in [1..numms] do
        msK:=MaximalSubgroupClassReps(ms[k]);
        if verbose=1 then
            Print("\n--- Checking the ", Size(msK), " second maximal subgroups below maximal subgroup ", k, " (of ", numms, " max subgps in ", nameG, ") ---\n");
#            AppendTo(outfile,"\n--- Checking the ", Size(msK), " second maximal subgroups below maximal subgroup ", k, " (of ", numms, " max subgps in ", nameG, ") ---\n");
        fi;
        for h in [1..Size(msK)] do
            H:=msK[h];
            corefree:=true;
            if core=0 and Order(H)>1 then   
                # check whether H is core-free
                if IsNormal(G,H) then
                    corefree:=false;
                else
                    coreH := Core(G,H);
                    if Order(coreH)>1 then
                        corefree:=false;
                    fi;
                fi;
            fi;
            if corefree then
                intHG:=IntermediateSubgroups(G,msK[h]);
                latsize:=Size(intHG.subgroups)+2;
                if verbose=1 then
                    Print("(",k,",",h,")\n          ", latsize, " = |L|;    intHG = ", intHG.inclusions, "\n");
                    AppendTo(outfile, intHG.inclusions, "; (", latsize, ") ", StructureDescription(G), " (",k,",",h,")  Index: ", Index(G,H), "; \n");
                elif latsize>=minL and latsize<=maxL then
                    if latsize=7 then
                        #                        Print("G = ", StructureDescription(G), "   H = ", StructureDescription(H), "  |G| = ", Order(G), "  |H| = ", Order(H), "\n");
                        Print("G = ", G, "   H = ", StructureDescription(H), "  |G| = ", Order(G), "  |H| = ", Order(H), "\n");
                        Print(">>>>>> ", latsize, ". ", TYPE, "Group(",i,",",j,"): (",k,",",h,") ", intHG.inclusions, " <<<<<<<<<<\n");
                    else
                    Print("G = ", G, "   H = ", StructureDescription(H), "  |G| = ", Order(G), "  |H| = ", Order(H), "\n");
                    # Print("G = ", StructureDescription(G), "   H = ", StructureDescription(H), "  |G| = ", Order(G), "  |H| = ", Order(H), "\n");
                    Print("  ", latsize, ". ", TYPE, "Group(",i,",",j,"): (",k,",",h,") ", intHG.inclusions, "\n");
                    fi;
                    AppendTo(outfile,  intHG.inclusions, ";  (", latsize, ") ", TYPE, "Group(",i,",",j,");  (",k,",",h,") Index:", Index(G,H),"\n");
                fi;
            fi;
        od;
    od;
end;

printUpperIntervalsInG2:=function(args)
    # printUpperIntervalsInG2:=function([G, datfile, i, j, core])
    # Find upper intervals, with at least 7 elements, above third maximal subgroups and below second maximal subgroups of G.
    # If core=1, allow the second maximal subgroups to contain a non-trivial normal subgroup of G.
    # If G is Alt(n) or Sym(n), set core=1, so as to not waste time looking for normal subgroups.
    local K, H, J, ms, msK, msH, h, i, j, k, l, intJK, numms, nameG, pathname, filename, G, outfile, nargin, verbose, latsize, core, corefree, coreJ;
    verbose:=0;
    G:=args[1];
    nargin := Length(args);
    if nargin < 5 then core:=0; else core:=args[5]; fi;  # the default is to allow H to have non-trivial core
    if nargin < 4 then j:=0; else j:=args[4]; fi;
    if nargin < 3 then i:=0; else i:=args[3]; fi;
    if nargin < 2 then 
        verbose:=1;
        nameG:=StructureDescription(G);
        pathname := getPathName();
        filename:=Concatenation(pathname, "ThirdMaxlUpperIntsInMaxSubsOf", nameG);
        if core=1 then filename:=Concatenation(filename, "WithCores"); fi;
        filename:=Concatenation(filename, ".dat");
        outfile := OutputTextFile(filename, false);
        SetPrintFormattingStatus(outfile, false);   # This prevents automatic indentation and line breaks.
        PrintTo(outfile, "Command used: PrintUpperIntervalsInG2( ", args, " ); \n\n");
    else
        outfile:=args[2];
    fi;
    ms:=MaximalSubgroupClassReps(G);
    numms:=Size(ms);
    if verbose=1 then
        Print("\n==== Checking the ", numms, " maximal subgroups of ", nameG, " ====\n");
#        AppendTo(outfile,"\n==== Checking the ", numms, " maximal subgroups of ", nameG, " ====\n");
    fi;
    
    for k in [1..numms] do
        K:=ms[k];
        msK:=MaximalSubgroupClassReps(K);
        if verbose=1 then
            Print("\n--- Checking the ", Size(msK), " second maximal subgroups below maximal subgroup ", k, " (of ", numms, " max subgps in ", nameG, ") ---\n");
        fi;
        for h in [1..Size(msK)] do
            H:=msK[h];
            msH:=MaximalSubgroupClassReps(H);
            if verbose=1 then
                Print("\n--- Checking the ", Size(msH), " third maximal subgroups below second maximal subgroup ", h, " (of ", Size(msK), " second max subgps in ", nameG, ") ---\n");
            fi;
            for j in [1..Size(msH)] do
                J:=msH[j];
                corefree:=true;
                if core=0 and Order(J)>1 then   
                    # check whether J is core-free in K
                    if IsNormal(K,J) then
                        corefree:=false;
                    else
                        coreJ := Core(K,J);
                        if Order(coreJ)>1 then
                            corefree:=false;
                        fi;
                    fi;
                fi;
                if corefree then
                    intJK:=IntermediateSubgroups(K,J);
                    latsize:=Size(intJK.subgroups)+2;
                    if verbose=1 then
                        # Print("(",k,",",h,",",j,")\n          ", latsize, " = |L|;    intJK = ", intJK.inclusions, "\n");
                        Print("(", latsize, ") ", intJK.inclusions, " G=", StructureDescription(G), "  (",k,",",h,",",j,"); ",
                                " K=", StructureDescription(K), ", J=", StructureDescription(J), ", [K:J]=", Index(K,J), "\n");
                        AppendTo(outfile, intJK.inclusions, "; (", latsize, ") G=", StructureDescription(G), "  (",k,",",h,",",j,"); ",
                                " K=", StructureDescription(K), ", J=", StructureDescription(J), ", [K:J]=", Index(K,J), "\n");
                    # elif latsize>6 then
                    #     Print("G = ", StructureDescription(G), "   H = ", StructureDescription(H), "  corefree = ", corefree, "\n");
                    #     Print(latsize, ". SmallGroup(",i,",",j,"): (",k,",",h,") ", intHG.inclusions, "\n");
                    #     AppendTo(outfile,  intHG.inclusions, ";  (", latsize, ") SmallGroup(",i,",",j,");  (",k,",",h,") Index:", Index(G,H),"\n");
                    fi;
                fi;
            od;
        od;
    od;
end;

                  
findUpperIntervalsQuick:=function(args)
    # findUpperIntervalsQuick:=function([n1, n2, minsz, maxsz, abelian, solvable, core])
    # Search among groups of order n1 <= |G| <=n2, and output all (isomorphism classes of) upper 
    # intervals L=[H,G] with 5<|L|<20.
    #
    # Inputs: n1,n2       search among groups G of order n1 <= |G| <= n2.
    #         abelian     (optional,default=1) if 0, don't include abelian groups in the search. 
    #         solvable    (optional,default=1) if 0, don't include solvable groups in the search.
    #         core        (optional,default=0) if 0, don't include intervals [H,G] when H is not core-free. 
    #
    # Output: file        The output file is called PrintAllUpperIntervalsMin6...
    #
    # Author: <williamdemeo@gmail.com>
    # Date: 2011.05.05
    #
    local i, j, k, m, r, s, pathname, filename, datfile, outfile, incls, newcnt, maxdepth,
          G, e, numsg, t, corefree, n1, n2, abelian, solvable, core, nargin, prefix, maxsz, minsz;
    
    nargin := Length(args);
    
    if nargin < 7 then core:=0; else core:=args[7]; fi;
    if nargin < 6 then solvable:=1; else solvable:=args[6]; fi;
    if nargin < 5 then abelian:=1; else abelian:=args[5]; fi;
    if nargin < 4 then maxsz:=100; else maxsz:=args[4]; fi;
    if nargin < 3 then minsz:=2; else minsz:=args[3]; fi;
    if nargin < 2 then Error("usage: findUpperIntervals([n1, n2, ...]);"); fi;
    
    n1:=args[1];  n2:=args[2];
    newcnt:=0;
    
    prefix := Concatenation("SecondMaximalMin", String(minsz), "Max", String(maxsz)); 
    if solvable=0 then prefix := Concatenation(prefix, "NonSolvable"); 
    elif abelian=0 then prefix := Concatenation(prefix, "NonAbelian"); fi;
    if core=1 then prefix := Concatenation(prefix, "Core"); fi;
    prefix:=Concatenation(prefix, "InSG", String(n1), "to", String(n2));
    
    pathname := getPathName();
    # This one stores output in human readable format:
    filename := Concatenation(pathname, prefix, ".out");
    outfile := OutputTextFile(filename, false);
    SetPrintFormattingStatus(outfile, false);   # This prevents automatic indentation and line breaks.
    PrintTo(outfile, "Command used: findUpperIntervalsQuick( ", args, " ); \n\n");
    
    # This one stores output in human readable format:
    filename := Concatenation(pathname, prefix, ".dat");
    datfile := OutputTextFile(filename, false);
    SetPrintFormattingStatus(datfile, false);   # This prevents automatic indentation and line breaks.
    PrintTo(datfile, "Command used: findUpperIntervalsQuick( ", args, " ); \n\n");
    
    for i in [n1..n2] do
        numsg := NumberSmallGroups(i);
        Print("Checking the ", numsg, " group(s) of order |G| = ", i, "...\n");
        AppendTo(outfile, "Checking the ", numsg, " group(s) of order |G| = ", i, "... \n");
        
        for j in [1..numsg] do
            G := SmallGroup(i,j);
            if abelian=0 and IsAbelian(G) then   # do nothing
            elif solvable=0 and IsSolvable(G) then  # do nothing
            else
                #                printUpperIntervalsInG([G,datfile,i,j,core]);
                findUpperIntervalsInG([G,minsz, maxsz, core, datfile,i,j]);
            fi;
        od;
    od;
end;;



findUpperIntervalsInPerfectGroups:=function(args)
    local i, j, k, m, r, s, pathname, filename, datfile, outfile, incls, newcnt,
          G, e, numsg, t, corefree, n1, n2, abelian, solvable, core, nargin, prefix;
    
    nargin := Length(args);
    
    core:=1;
    
    n1:=args[1];  n2:=args[2];
    newcnt:=0;
    
    prefix := "SecondMaxlUpperIntervalsPerfect";
    prefix:=Concatenation(prefix, String(n1), "to", String(n2));
    
    pathname := getPathName();
    # This one stores output in human readable format:
    filename := Concatenation(pathname, prefix, ".out");
    outfile := OutputTextFile(filename, false);
    SetPrintFormattingStatus(outfile, false);   # This prevents automatic indentation and line breaks.
    PrintTo(outfile, "Command used: findUpperIntervalsInPerfectGroups( ", args, " ); \n\n");
    
    # This one stores output in human readable format:
    filename := Concatenation(pathname, prefix, ".dat");
    datfile := OutputTextFile(filename, false);
    SetPrintFormattingStatus(datfile, false);   # This prevents automatic indentation and line breaks.
    PrintTo(datfile, "Command used: findUpperIntervalsQuick( ", args, " ); \n\n");
    
    for i in [n1..n2] do
        numsg := NumberPerfectGroups(i);
        Print("Checking the ", numsg, " group(s) of order |G| = ", i, "...\n");
        AppendTo(outfile, "Checking the ", numsg, " group(s) of order |G| = ", i, "... \n");
        
        for j in [1..numsg] do
            G := PerfectGroup(i,j);
            printUpperIntervalsInG([G,datfile,i,j,core]);
        od;
    od;
end;;
    

findUpperIntervalsInPrimitiveGroups:=function(args)
    # findUpperIntervalsInPrimitiveGroups([n1, n2, OSType, Nonsolvable, minL, maxL]);
    # Example: findUpperIntervalsInPrimitiveGroups([1, 100, "1", 1]);
    #          Searches for second maximal upper intervals L with minL \leq |L| \leq maxL
    #          in nonsolvable primitive perm groups of orders 1 to 100 with ONanScottType="1"
    local i,j, k, m, r, s, pathname, filename, datfile, outfile, incls, newcnt,
          grps, NS, OSType, G, e, numsg, t, corefree, n1, n2, abelian,
          solvable, nargin, prefix, numprim, maxL, minL; 
    
    nargin := Length(args);
    if nargin < 6 then maxL:=0; else maxL:=args[6]; fi;
    if nargin < 5 then minL:=0; else minL:=args[5]; fi;
    if nargin < 4 then NS:=0; else NS:=args[4]; fi;
    if nargin < 3 then OSType:=false; else OSType:=args[3]; fi;
    if nargin < 2 then Error("usage: findUpperIntervalsInPrimitiveGroups([n1, n2, ...]);"); fi;
    
    n1:=args[1];  n2:=args[2];
    newcnt:=0;
    
    prefix := "SecondMaxlUpIntInPrim";
    prefix:=Concatenation(prefix, String(n1), "to", String(n2));
    if NS>0 then
        prefix:=Concatenation(prefix, "NS");
    fi;
    if OSType then
        prefix:=Concatenation(prefix, "_OSType", OSType);
    fi;
    if maxL>0 then
        prefix:=Concatenation(prefix, "_Min", String(minL), "Max",String(maxL));
    fi;
    
    pathname := getPathName();
    # This one stores output in human readable format:
    filename := Concatenation(pathname, prefix, ".out");
    outfile := OutputTextFile(filename, false);
    SetPrintFormattingStatus(outfile, false);   # This prevents automatic indentation and line breaks.
    PrintTo(outfile, "Command used: findUpperIntervalsInPrimitiveAffineGroups( ", args, " ); \n\n");
    
    # This one stores output in human readable format:
    filename := Concatenation(pathname, prefix, ".dat");
    datfile := OutputTextFile(filename, false);
    SetPrintFormattingStatus(datfile, false);   # This prevents automatic indentation and line breaks.
    PrintTo(datfile, "Command used: findUpperIntervalsInPrimitiveAffineGroups( ", args, " ); \n\n");
    
    # # it's okay to do it this way, but it makes it harder to locate the group later.
    # grps:=AllPrimitiveGroups(NrMovedPoints, [n1..n2], ONanScottType, 1);
    # for G in grps do
    #     printUpperIntervalsInG([G,datfile,0,0,core]);
    # od;
    
    for i in [n1..n2] do
        numprim:=NrPrimitiveGroups(i);
        for j in [1..numprim] do
            G:=PrimitiveGroup(i,j);
            if NS=0 or IsSolvable(G) then
                if (not OSType) or ONanScottType(G)=OSType then
                    printUpperIntervalsInG([G,datfile,i,j,minL,maxL]);
                fi;
            fi;
        od;
    od;

end;;

findUpperIntervalsInPrimitiveAffineGroups:=function(args)
    local i,j, k, m, r, s, pathname, filename, datfile, outfile, incls, newcnt, grps,
          G, e, numsg, t, corefree, n1, n2, abelian, solvable, core, nargin, prefix, numprim;
    
    nargin := Length(args);
    
    core:=1;
    
    n1:=args[1];  n2:=args[2];
    newcnt:=0;
    
    prefix := "SecondMaxlUpperIntInPrimitiveAffine";
    prefix:=Concatenation(prefix, String(n1), "to", String(n2));
    
    pathname := getPathName();
    # This one stores output in human readable format:
    filename := Concatenation(pathname, prefix, ".out");
    outfile := OutputTextFile(filename, false);
    SetPrintFormattingStatus(outfile, false);   # This prevents automatic indentation and line breaks.
    PrintTo(outfile, "Command used: findUpperIntervalsInPrimitiveAffineGroups( ", args, " ); \n\n");
    
    # This one stores output in human readable format:
    filename := Concatenation(pathname, prefix, ".dat");
    datfile := OutputTextFile(filename, false);
    SetPrintFormattingStatus(datfile, false);   # This prevents automatic indentation and line breaks.
    PrintTo(datfile, "Command used: findUpperIntervalsInPrimitiveAffineGroups( ", args, " ); \n\n");
    
    # # it's okay to do it this way, but it makes it harder to locate the group later.
    # grps:=AllPrimitiveGroups(NrMovedPoints, [n1..n2], ONanScottType, 1);
    # for G in grps do
    #     printUpperIntervalsInG([G,datfile,0,0,core]);
    # od;
    
    for i in [n1..n2] do
        numprim:=NrPrimitiveGroups(i);
        for j in [1..numprim] do
            G:=PrimitiveGroup(i,j);
            if ONanScottType(G)="1" then
                printUpperIntervalsInG([G,datfile,i,j,core,"Primitive"]);
            fi;
        od;
    od;

end;;

findUpperIntervalsInPrimitiveNonsolvableGroups:=function(args)
    local k, m, r, s, pathname, filename, datfile, outfile, incls, newcnt, grps,
          G, e, numsg, t, corefree, n1, n2, abelian, solvable, core, nargin, prefix;
    
    nargin := Length(args);
    
    core:=1;
    
    n1:=args[1];  n2:=args[2];
    newcnt:=0;
    
    prefix := "SecondMaxlUpperIntInPrimitiveNonsolvable";
    prefix:=Concatenation(prefix, String(n1), "to", String(n2));
    
    pathname := getPathName();
    # This one stores output in human readable format:
    filename := Concatenation(pathname, prefix, ".out");
    outfile := OutputTextFile(filename, false);
    SetPrintFormattingStatus(outfile, false);   # This prevents automatic indentation and line breaks.
    PrintTo(outfile, "Command used: findUpperIntervalsInPrimitiveNonsolvableGroups( ", args, " ); \n\n");
    
    # This one stores output in human readable format:
    filename := Concatenation(pathname, prefix, ".dat");
    datfile := OutputTextFile(filename, false);
    SetPrintFormattingStatus(datfile, false);   # This prevents automatic indentation and line breaks.
    PrintTo(datfile, "Command used: findUpperIntervalsInPrimitiveNonsolvableGroups( ", args, " ); \n\n");
    
    grps:=AllPrimitiveGroups(NrMovedPoints, [n1..n2], IsSolvable, false);
    for G in grps do
        printUpperIntervalsInG([G,datfile,0,0,core]);
    od;

end;;
    
findUpperIntervalsInPrimitiveGroups:=function(args)
    # findUpperIntervalsInPrimitiveGroups([n1, n2, NonSolvable, AOSType]);
    local i,j,k, m, r, s, pathname, filename, datfile, outfile, incls, newcnt, grps, AOSType, numprim,
          G, e, numsg, t, corefree, n1, n2, abelian, solvable, core, nargin, prefix, NonSolvable;
    nargin := Length(args);
    prefix := "SecondMaximalUpperIntInPrimitive";
    n1:=args[1];  n2:=args[2];
    
    core:=1;  # not using this now
    
    if nargin < 4 then  AOSType:=0; else AOSType:=args[4]; fi;
    if nargin < 3 then NonSolvable:=0; else NonSolvable:=args[3]; fi;
    if NonSolvable>0 then
        prefix:=Concatenation(prefix, "NonSolvable");
    fi;
    if AOSType>0 then
        prefix:=Concatenation(prefix, "ONanScottType", String(AOSType));
    fi;
    newcnt:=0;
    
    prefix:=Concatenation(prefix, String(n1), "to", String(n2));
    
    pathname := getPathName();
    # This one stores output in human readable format:
    filename := Concatenation(pathname, prefix, ".out");
    outfile := OutputTextFile(filename, false);
    SetPrintFormattingStatus(outfile, false);   # This prevents automatic indentation and line breaks.
    PrintTo(outfile, "Command used: findUpperIntervalsInPrimitiveNonsolvableGroups( ", args, " ); \n\n");
    
    # This one stores output in human readable format:
    filename := Concatenation(pathname, prefix, ".dat");
    datfile := OutputTextFile(filename, false);
    SetPrintFormattingStatus(datfile, false);   # This prevents automatic indentation and line breaks.
    PrintTo(datfile, "Command used: findUpperIntervalsInPrimitiveNonsolvableGroups( ", args, " ); \n\n");
    
    for i in [n1..n2] do
        Print("Checking the ", NrPrimitiveGroups(i), " primitive group(s) of degree ", i, "...\n");
        numprim:=NrPrimitiveGroups(i);
        for j in [1..numprim] do
            G:=PrimitiveGroup(i,j);
            if AOSType=0 or ONanScottType(G)=String(AOSType) then
                if NonSolvable=1 and IsSolvable(G) then
                        # do nothing
                else
                    printUpperIntervalsInG([G,datfile,i,j,core,"Primitive"]);
                fi;
            fi;
        od;
    od;

end;;
    

findUpperIntervalsIn1536:=function(args)
    # findUpperIntervalsQuick:=function([n1, n2, abelian, solvable, core])
    # Search among groups of order n1 <= |G| <=n2, and output all (isomorphism classes of) upper 
    # intervals L=[H,G] with |L|>6.
    #
    # Inputs: n1,n2       search among groups G:=SmallGroup(1536,n) for n1 <= n <= n2.
    #         abelian     (optional,default=1) if 0, don't include abelian groups in the search. 
    #         solvable    (optional,default=1) if 0, don't include solvable groups in the search.
    #         core        (optional,default=0) if 0, don't include intervals [H,G] when H is not core-free. 
    #
    # Output: file        The output file is called PrintAllUpperIntervalsMin6...
    #
    # Author: <williamdemeo@gmail.com>
    # Date: 2011.05.05
    #
    local i, j, k, m, r, s, pathname, filename, datfile, outfile, incls, newcnt, maxdepth,
          G, e, numsg, t, corefree, n1, n2, abelian, solvable, core, nargin, prefix;
    
    nargin := Length(args);
    
    if nargin < 5 then core:=0; else core:=args[5]; fi;
    if nargin < 4 then solvable:=1; else solvable:=args[4]; fi;
    if nargin < 3 then abelian:=1; else abelian:=args[3]; fi;
    if nargin < 2 then Error("usage: findUpperIntervals([n1, n2, ...]);"); fi;
    
    n1:=args[1];  n2:=args[2];
    newcnt:=0;
    
    prefix := "PrintAllUpperIntervalsIn1536";
    if solvable=0 then prefix := Concatenation(prefix, "NonSolvable"); 
    elif abelian=0 then prefix := Concatenation(prefix, "NonAbelian"); fi;
    if core=1 then prefix := Concatenation(prefix, "Core"); fi;
    prefix:=Concatenation(prefix, String(n1), "to", String(n2));
    
    pathname := getPathName();
    # This one stores output in human readable format:
    filename := Concatenation(pathname, prefix, ".out");
    outfile := OutputTextFile(filename, false);
    SetPrintFormattingStatus(outfile, false);   # This prevents automatic indentation and line breaks.
    PrintTo(outfile, "Command used: findUpperIntervalsIn1536( ", args, " ); \n\n");
    
    # This one stores output in human readable format:
    filename := Concatenation(pathname, prefix, ".dat");
    datfile := OutputTextFile(filename, false);
    SetPrintFormattingStatus(datfile, false);   # This prevents automatic indentation and line breaks.
    PrintTo(datfile, "Command used: findUpperIntervalsQuick( ", args, " ); \n\n");
    for i in [n1..n2] do
        G := SmallGroup(1536,i);
        if abelian=0 and IsAbelian(G) then   # do nothing
        elif solvable=0 and IsSolvable(G) then  # do nothing
        else
            printUpperIntervalsInG([G,datfile,1536,i,core]);
        fi;
    od;
end;;








canonicalForm:=function(incl)
    # Put covering relations in "canonical" form.
    # This routine does NOT work well.  It sometimes leaves the coverings arranged
    # so that the maximum number does not appear in the last covering relation.
    # DEBUG: figure out a better canonical form and improve this routine.
    local n, m, j, i, x, y, z, newincl, f, count, flag, p, tmp;
    if not IsList(incl) then
        Error("usage: canonicalForm( <list> );");
    fi;
    incl := SSortedList(incl);
    n:=Length(incl);
    m:=Maximum(Maximum(incl));
    count:=0;
    i:=2;
    while i<n-1 do
        if incl[i][2] > incl[i+1][2] then
            flag:=1;
            if incl[i][1] <> incl[i+1][1] then
                p:=Positions(List([1..n], x->incl[x][1]), incl[i][1]);
                if incl[i+1][2] in List(p, x->incl[x][2]) then
                    flag:=0;  # don't need to permute elements since
                fi;           # incl[i][2] > incl[i+1][2] is necessary since the
                              # covering [incl[i][1] incl[i+1][2]] already appeared.
            fi;
            if flag=1 then
                y:=incl[i][2];   z:=incl[i+1][2];
                # swap y and z values
                f:=[1..m+1]; f[y+1]:=z+1; f[z+1]:=y+1;
                newincl:=[[ ]];
                for j in [1..n] do
                    newincl[j]:=List(incl[j], x->(f[x+1]-1)); 
                od;
                incl:=SSortedList(newincl);
                i:=1;
            fi;
        fi;
        i:=i+1;
        count:=count+1;
        if count > 500 then
            Print("\nWARNING: didn't finish puting  ", incl, "  in canonical form \n");
            return incl;
        fi;
    od;
    # Make sure the last value is the max (if not, swap it)
    if incl[n][2]<> m then
        p:=Positions(List([1..n-1],x->incl[x][2]),m);
        tmp:=incl[n];
        incl[n]:=incl[p[Size(p)]];
        incl[p[Size(p)]]:=tmp;
    fi;
    return incl;
end;

