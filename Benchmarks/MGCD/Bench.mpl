
#######################################################################################
#Connv2Root takes a polynomial (in natural form) and converts it to its RootOf version:
#######################################################################################
ConvNat2Root:=proc(f,Z,M,Xmin) #f is the polynomial [x1,x2,...xk,z1,...zn]
local n,H,i,newf;
    n := nops(Z);
    if n <> nops(M) then
        error "length mismatch: nops(Z)=%d, nops(M)=%d", n, nops(M);
    end if;
    H:={ seq( Z[i] = RootOf(M[i],Xmin[i]), i=1..n ) };
        newf:=subs(H,f);
    return(newf);
end proc:
###############################################################################################################
#Conv2Alg takes a polynomial (in RDP form) and converts it to its Rootof version:
#input: polynomial f in the form of Algebraic:-RecursiveDensePolynomials:-rpoly, M=list of minimal polynomials
#output: polynomial f in the form of RootOf
###############################################################################################################
ConvAlg2Root:=proc(f,M) 
uses RDP=Algebraic:-RecursiveDensePolynomials;
local n,H,i,newf,X,m,Xmin,W;
    X:=getvars(f); #The polynomial and minimal polynomials' variables
    m:= nops(X); #Number of variables
    n := nops(getexts(f)); #Number of algebraic numbers (min polys variables)
    Xmin:=[seq(X[i], i = m .. m-n+1, -1)];  #minpolys variables
    H:={ seq( Xmin[i] = RootOf(M[i],Xmin[i]), i=1..n ) };
        newf:=subs(H,RDP:-rpoly(f));
    return(newf);
end proc:
###################################################################################
# fact takes N and returns the list of factorizations of N into factors 2 or 3,
# in the style: [ big_factor, then (k-1) minimal factors each equal to 2 or 3 ].
# If N has any prime factor other than 2 or 3, it raises an error.
# If the total number of prime factors (a+b) < 2, it returns [].
#It keeps only one factorization per length
#Example: If N=16, then  fact(16)=[[2, 2, 2, 2], [4, 2, 2], [8, 2]]
###################################################################################
fact:= proc(N)
local m, a, b, k, Fact, cand, i,j,r;
    m := N; a := 0; b := 0;

    # count powers of 2 and 3
    while m mod 2 = 0 do m := m/2; a := a+1 end do;
    while m mod 3 = 0 do m := m/3; b := b+1 end do;
    if m <> 1 then error "N has prime factors other than 2 or 3" fi;

    if a + b < 2 then
        return [];
    end if;

  #  Fact := [seq(0,i=1..a+b-1)];
  Fact:=[seq(0,i=1..a+b-1)];

    # For each length k, take the first valid candidate
    for k from 2 to a+b do
        for r from max(0,(k-1)-b) to min(k-1,a) do
            cand := 2^(a-r) * 3^(b-(k-1-r)),
                      seq(2,i=1..r),
                      seq(3,j=1..(k-1-r)) ;
            Fact[k-1] := [cand];
            break;  # keep only the first candidate for this length
        od;
    od;
 return [ op(ListTools:-Reverse([op(Fact)])), [N] ]; # longest factorization first
end proc:


##########################################################################
# Build the Minlist array from N by calling fact(N).
# Example for N = 2^2*3^3:
# L = [[2,2,3,3,3],[4,3,3,3],[3,6,6],[12,3],[36,3]]
# Minlist[1] = [ z1^2-2, z2^2-3, z3^3-5, z4^3-7, z5^3-11 ]
# Minlist[2] = [ LAminpoly(z1^2-2, z2^2-3), z3^3-5, z4^3-7, z5^3-11 ], etc.
###########################################################################
Minpolylist := proc(N,numext) #second number is the #ext
uses RDP=Algebraic:-RecursiveDensePolynomials;
local L, L1, n, P, i, k, r, prod, zfresh,Xminpol,minpol,gama,nest,NL,Xmin,NXmin,R,newXmin,gam,j,flag,mins;
    
    flag:=0;
    L := fact(N); #When N=2^3*3^2, L=[[2,2,2,3,3],[4,2,3,3],[8,3,3],[24,3]]
    NL:=nops(L);
    L1 := L[1];
    n  := nops(L1);
    zfresh := z[n+1];
    #Base polynomials P[i] = z_i^{L1[i]} - ithprime(i)
    P := [seq( (z[i])^(L1[i]) - ithprime(i), i=1..n ) ]; #This extension has the max lenght
    if numext=n or not type(numext,integer) then
        return(P);
    fi;
    #For calling LAminpoly
    Xmin:=ListTools:-Reverse([seq( (z[i]), i=1..n )]);
    NXmin:=nops(Xmin);
    R := [seq(0,i=1..NL)]; #the resulted list R[1]=[z1^2-2,z2^2-3,z3^2-5,z4^3-7,z5^3-11]
    R[1]:=P;
      for i from 2 to NL do #it used to be 2
           newXmin:= [op(indets(R[i-1][1])),op(indets(R[i-1][2]))];
           gam:=op(indets(R[i-1][1]))+op(indets(R[i-1][2]));
           gama := Algebraic:-RecursiveDensePolynomials:-rpoly(gam, ListTools:-Reverse(newXmin),[R[i-1][1],R[i-1][2]]);
           R[i][1]:=LAMinpoly([R[i-1][1],R[i-1][2]],gama,newXmin,zfresh,p)[1];
           zfresh := z[n+i];
           R[i]:=[R[i][1],seq(R[i-1][j],j=3..nops(R[i-1]))];
           Xmin:=[zfresh,op(Xmin)];
           NXmin:=NXmin+1;
           if numext=nops(R[i]) then flag:=1;  mins:=R[i]; return(mins); fi;
      od;
      if flag=0 then error "A field of degree=%d cannot have an extension of length %d", N, numext; fi;
return (mins);
end proc:
###############################################################################################################
#####################################################################################################################
#minpolygen creats dense algebraic coefficients for constructing the cofactors and gcd
#takes: c=random proc, mins:list of minimal polynomials, and Xmin=list of the minimal polynomials' variables
###########################################
minpolygen := proc(c, mins::list, Xmin::list)
    local n, d, Cof, make, j,i;

    n := nops(Xmin);
    d := [seq(degree(mins[i], Xmin[i]), i=1..n)];   # degree limits

    # random nonzero coefficient
    Cof := proc()
        local v;
        do v := c(); if v <> 0 then return v fi; od;
    end proc;

    # recursive dense polynomial builder
    make := proc(k)
        local j, s;
        if k = 0 then
            return Cof();
        else
            s := 0;
            for j from 0 to d[k]-1 do
                s := s + Xmin[k]^j * make(k-1);
            od;
            return s;
        end if;
    end proc;

    expand(make(n));
end proc:
    
################################################################################################################
#takes: c=random proc, nvar=#variables, tdeg:Total degree of a,b,c, degfield= degree of the field,  
#numext= # of exts
#returns: a,b,g with total degree tdeg in recden form in a field with degree "degfield" and "numext" extentions
################################################################################################################
#Polygen Michael's dense version:
polygen:= proc(c, nvar::nonnegint, tdeg::nonnegint, gcddeg::nonnegint,
                degfield, numext)
    uses RDP = Algebraic:-RecursiveDensePolynomials;
    local mins, Xmin, Xpoly, XT, pickSS, a, b, g,m,i;

    mins  := Minpolylist(degfield, numext);
    Xmin  := [seq(op(indets(m, indexed)), m in mins)];
    Xpoly := [seq(x[i], i=1..nvar)];
    XT    := [op(Xpoly), op(ListTools:-Reverse(Xmin))];

    # Algebraic-number coefficients are made by PickSS
    #pickSS := () -> minpolygen(c, mins, Xmin);
    pickSS := () -> minpolygen(c,mins,Xmin);
    # Build(k,d): dense poly in x[1]..x[k] of degree d in x[k],
    # with coefficients from pickSS().
    local Build;
    Build := proc(k::nonnegint, d::nonnegint)
        local i, z, xk;
        if k = 0 then
            # Base: return a NON-ZERO coefficient from the coeff ring
            if nops(Xmin) = 0 then
                # No extensions → fall back to integers from c()
                do z := c(); if z <> 0 then return z fi od;
            else
                do z := pickSS(); if z <> 0 then return z fi od;
            fi;
        else
            xk := x[k];
            return add( Build(k-1, d) * xk^i, i=0..d );
        fi;
    end proc;

    # Dense polynomials
    a := Build(nvar, (tdeg-gcddeg));
    b := Build(nvar, (tdeg-gcddeg));
    g := Build(nvar, gcddeg);

    # RDP format
    a := RDP:-rpoly(a, XT, mins);
    b := RDP:-rpoly(b, XT, mins);
    g := RDP:-rpoly(g, XT, mins);

    return a, b, g, mins;
end proc:
##########################################################################################
#flagalg:=MGCDRec      #uses MGCD (Recden version) to compute the gcd
#flagalg:=MGCD         #uses MGCD (RDP=Algebrai:-RecursiveDensePolynomials version) to compute the gcd
#flagalg:=Algebraic:-Gcd       #uses Algebraic:-GreatestCommonDivisor(f1,f2) to compute the gcd
#flagalg:=evala@Gcd           #uses evala(Gcd(f1,f2))
#########################################################################################
GCDcomputer:=proc(flagalg,f1,f2,p::nonnegint:=0) #support for when p=0
  
   if p<>0  then
        if flagalg=Gcd  then #flagalg=Algebraic:-Gcd option characteristic
            return flagalg(f1,f2) mod p;
        elif flagalg=Algebraic:-Gcd then
            return  flagalg(f1,f2,'characteristic' =p);
        else 
            return(flagalg(f1,f2,p));
            fi;
    else
        return(flagalg(f1, f2));
     fi;

end proc:
#################################

Benchmain:=proc(flagalg::Or(function,procedure),
    nvar::Or(nonnegint,list),
    tdeg::Or(nonnegint,list),
    gcddeg::Or(nonnegint,list),
    degfield::Or(nonnegint,list),
    numext::Or(nonnegint,list,name),p::nonnegint:=0) #flagpol is redundant
 uses RDP = Algebraic:-RecursiveDensePolynomials;
local c,a0,b0,header, R,F1,F2,t,k,G,TA,ncols,i,j,d,timings,Indx,var,mins,Args,lb,ub,counter,S,dg,G0,Nmin,Nrange,Range,J,T,Np;
#we use randomize to create pseudo- random polys in polygen and Minpolylist
   Args:=[nvar, tdeg, gcddeg, degfield, numext];
   timings := true:
   counter:=0; #counts the number of times gcd=the designated gcd
   #Header is the first row of the matrix R which includes all the results
   header := ["dF", "#ext", "#var",
               "Tdeg(f1)", "Tdeg(f2)", "Tdeg(g)","Tdeg(a)","Tdeg(b)",
               "Tdeg(GCD)", "Time", "Np"];
    ncols := nops(header);
    #Indx presents which argument is changing
    Indx:=ListTools:-SelectFirst(type,Args,list,output=indices); 
    Range:=Args[Indx]; 
    if Indx=3 then
       Nrange:=nops(Range)+1
    else
       Nrange:=4*nops(Range)+1; #number of rows of R
    fi;
    #Matrix R will hold all results (including header). dimesion of the matrix depends on the # of rows (# of iterations) which depends on the bechmark
    R := Matrix(Nrange+1,ncols,datatype=anything); #+2 because we have the 1st row as the header
    R[1] := Vector(header);
    j:=2; #counts the rows of Matrix R since the for loop does not usually start from 1 or 2.                       
   
    for i in Range do
        if Indx=2  then
           T:=i 
        else 
           T:=tdeg;
        fi;
        if Indx=3 then 
           J:=[1]
        else
           J:=[1,floor(T/4),ceil(T/2),ceil(3*T/4)];
        fi;
        for k in J do
        #replace Indx with i and degree of the gcd to be k
        if Indx=3 then 
           S:=op(subsop(Indx = i, Args)); 
        else
           S:=op(subsop(Indx=i,3=k,Args)); 
        fi;
        randomize(100+i);
        if p=0 then 
           c:=rand(100);
        else
           c:=rand(p);
        fi;
        a0,b0,G0,mins:=polygen(c,S);
        #generate random polynomials f1 and f2 with G0 as their designated gcd
        F1:=RDP:-mulrpoly(a0,G0);
        F2:=RDP:-mulrpoly(b0,G0);
        CodeTools:-Profiling:-Profile(flagalg);  
        try  
            t := time():
               G := timelimit(100, GCDcomputer(flagalg,F1, F2,p));
            TA  :=time()-t; 
            Np:=G[2];
            dg:= RDP:-tdegrpoly(G[1]);  
              CodeTools:-Profiling:-PrintProfiles(flagalg);
              CodeTools:-Profiling:-UnProfile(flagalg);
              #Check the correctness  
              if p=0 and not RDP:-divrpoly(G[1],G0) then
                  error "The divisiblity check failed for  algorithm=%1 for f1=%2,f2=%3", flagalg, F1,F2; 
              fi;

        catch  "time expired": 
               TA  := FAIL; 
               dg:=FAIL; 
             
        catch:   
                dg:=FAIL; 
               TA:=StringTools:-FormatMessage(lastexception[2..-1]); #lastecxeption contains the error

        end try;
        # Append row: degrees + time
        Nmin:=nops(mins);
        d:=mul(degree(mins[i]),i=1..Nmin);
        var:=nops(getvars(F1))-Nmin;
        R[j]:= Vector([ d, Nmin, var, 
             RDP:-tdegrpoly(F1), RDP:-tdegrpoly(F2), RDP:-tdegrpoly(G0), RDP:-tdegrpoly(a0), RDP:-tdegrpoly(b0),
             dg,  TA, Np ]);
        j:=j+1;        
        end do;
   end do;
     return Matrix(R); #save in excel #Export(R,name of the file) DocumentTools:-Tabulate(R); # Generate table :-)
end proc:


#This makes the rings consistent if one of them is Q and the other one is Q(alpha_1,...alphan)
Conv2LargerRing:=proc(A0::POLYNOMIAL,B0::POLYNOMIAL) uses RDP=Algebraic:-RecursiveDensePolynomials;
local A1,B1, RingA, RingB, CharA,XA,EA,CharB,XB,EB;
   RingA:=getring(A0);
   RingB:=getring(B0);
   A1,B1:=A0,B0;
   CharA,XA,EA := op(RingA);
   CharB,XB,EB:=op(RingB);
   if RingA<>RingB then
      if nops(EA)>nops(EB) then 
         B1:=RDP:-rpoly(RDP:-rpoly(B0),[CharA,XA,EA]);
      else 
         A1:=RDP:-rpoly(RDP:-rpoly(A0),[CharB,XB,EB]);
      fi;
   fi;
   return(A1,B1,ring);
end proc: