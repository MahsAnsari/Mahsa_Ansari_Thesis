#MGCD
with(ListTools): 
#Takes A,B in Q[z]/<m(z)>[x1,..xn] and gives GCD(A,B)  
MGCD1:= proc(A1,B1,sprime)
global MEAc;
local A,B,ringA,X,Xpoly,Minpolys,cc,i,m,n,Xmin,conta,contb,k,ap,bp,LCap,LCbp,lmap,lmbp,minmon,H,prod,p,Ap,Bp,Cp,lcCp,lmCp,least,CRT,H2,test1,test2,summon,irat,M,gama,gamma,phimatrix,invphimatrix,PhiAp,PhiBp, lcmintest,xx,yy,ca,cb,nca,ncb,C,counter,j,s,nfac,fac,ss,l,LA,Rand,ZD,L,AL,BL,GCDL,wt,LCH2,slc,randfunction,minpolys,st,tt,laminpolytime,pgcdtime,Np,timings, Goodp;
MEAc:=0;
#We use semi of the inputs to eliminate fractions
timings:=true;
   tt := time();
   laminpolytime := 0;
   pgcdtime := 0;
   A:=semi(A1);
   B:=semi(B1);
   checkconsistency(A,B,alpha);
   ringA:=getring(A);
   #get the whole variables
   X:=getvars(A);
   n:=nops(X);
   #get the minimal polynomials
   minpolys:=getalgexts(A);  #The list of minimal polynomials
   m:=nops(minpolys); 
   #get the polynomials' variables
   Xpoly:=X[1..n-m];
   #get the minimal polynomials' variables
   Xmin:=Reverse(X[n-m+1..n]); 
   
   #We need to convert minpolys from rpoly to simple polynomials
   Minpolys := map(rpoly,minpolys);
   ap, bp:= A,B;
   #k is the nops of the variables of polynomials
   k:= nops(Xpoly);
   H:=[];
   Np:=0;
    Goodp:=0;
   #we do not need bound when we are using iratrecon since the loop terminates when iratrecon gives the proper answer
   if nargs=2 then p := 2^31; else p:= sprime-1; fi;
   #The main loop
   while true do
   #recognizing lc-bad and det-bad primes
      do
         p:= nextprime(p);
         Np:=Np+1;
         printf("MGCD1:prime=%d\n",p);
         lcmintest:=true;
         for i to m do   #p must not divide lc of ^M_i
              if den(minpolys[i]) mod p=0 then lcmintest:=false; fi;
         od;
         #p is a bad prime if p|LC(A) 
         if rpoly(lcrpoly(A,Xpoly)) mod p = 0 then 
            printf("p=%d is an lc-bad prime\n",p); 
         fi;
      until rpoly(lcrpoly(A,Xpoly)) mod p <> 0
      and
      #As we used the semi of inputs as our inputs, we do not need to check if den(A)& den(B) mod p<>0
       lcmintest=true;
      #If p | lcoeff of A^,M^, where A^ is the semi associate of A and m^ is the semi-associate of the minimal polynomial then p is a lc-bad prime.
     
         Rand:=rand(1..p-1);
         C:=[seq(Rand(),i=1..m-1)];
         gama := Xmin[1]+add(C[i]*Xmin[i+1],i=1..m-1);
         gamma := phirpoly(rpoly(gama,getcofring(A)),p);
         st := time();
         LA:=LAMinpoly(Minpolys,p,gamma,Xmin,X[n]);
         laminpolytime := laminpolytime + time()-st;
         if LA=FAIL then 
            printf("p=%d is a det-bad prime or C=%a is an inappropriate list of constants\n",p,C); 
            next;
         fi;

 M,phimatrix,invphimatrix:=LA;
#printf("gamma:=%a and M(z)=%a\n",gama,M);
   
   Ap:= phirpoly(ap,p); #Now everything is in Zp
   Bp:= phirpoly(bp,p);
   PhiAp:=Phi(Ap,Minpolys,Xmin,Xpoly,1,M,phimatrix,invphimatrix); #In Z_p(gamma)
   PhiBp:=Phi(Bp,Minpolys,Xmin,Xpoly,1,M,phimatrix,invphimatrix);
   st := time();
   Cp:=traperror(PGCD(PhiAp,PhiBp,p));
   pgcdtime := pgcdtime+time()-st;
   #if there is a zero divisor then go to the first loop and change the prime
   #print Z-D primes
    if Cp=lasterror and nops([Cp])=2 and Cp[1]="inverse does not exist" then
      ZD:=Cp[2];  printf("p=%d is a ZD prime ZD=%a\n",p,ZD);
      next;
   elif Cp=lasterror then error lasterror;
   fi;

   #When the modular gcd is constant we are done!
   if degrpoly(Cp)=0 then printf("Cp=%a is a constant",Cp); return(rpoly(1,X)) fi;
   Cp:=Phi(Cp,Minpolys,Xmin,Xpoly,-1,M,phimatrix,invphimatrix);
   getring(Cp);
   lcCp:= lcrpoly(Cp,Xpoly[1..k-1]);
   lmCp:=rpoly(lmrpoly(Cp,Xpoly[1..k-1],X));
   if not assigned(minmon) then 
      Goodp:=1;
      CRT:=Cp;
      minmon:=lmCp;
      summon:=minmon;
      least:=minmon;
      H:=[Cp];
   else
   summon:=lmCp+minmon;
   least:=rpoly(tmrpoly(rpoly(summon,X),Xpoly,X));
   Cp:= scarpoly(invrpoly(lcrpoly(Cp)),Cp);
   #Test for unlucky primes
      if lmCp = least and minmon<>least then  
         if p>sprime then printf("p=%d and All the previous primes were unlucky\n",p); fi;
         H:=[Cp];
         CRT:=Cp; 
         Goodp:=1;
         minmon:=least;
      elif  lmCp = least and minmon= least then
         H:=[op(H),Cp];
          Goodp:= Goodp+1;
         CRT:=ichremrpoly(map(retextsrpoly,H));
      elif lmCp<>least then  
         printf("%a is an unlucky prime\n",p);
         Goodp:= Goodp-1;
      fi;
   fi;
   irat:=irrrpoly(CRT);
   if  irat<> FAIL then 
      H2:=subsop(1=ringA,irat);#We do not use the bound.When RNR has a correct solution the loop termintes.
   #Make our algorithm a Monte Carlo algorithm
       randfunction:=rand(p);
      do
        #Make our algorithm a Monte Carlo algorithm
           L:=[seq(Xpoly[i]= randfunction(), i=2..k)];
           AL, BL, GCDL:= evalrpoly(A,L), evalrpoly(B,L), evalrpoly(H2,L);
       until degrpoly(GCDL,Xpoly[1])=degrpoly(H2,Xpoly[1]);

      if divrpoly(AL,GCDL) and divrpoly(BL,GCDL) then
         tt := time()-tt;
         if timings=true then 
             printf("MGCD1: time=%.3f  LAminpoly=%.3f  PGCD=%.3f Np=%d  Goodp=%d NMEAc=%d\n",tt,laminpolytime,pgcdtime,Np, Goodp,MEAc); 
         fi;
         return (H2);
      fi;
    fi;
od;
end:
