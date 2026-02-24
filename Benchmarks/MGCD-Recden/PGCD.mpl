#PGCD
#X is the list of the polynomials' variables, XT is the list of the whole variables
#We did not use minpoly in PGCD So PGCD is the same for single & multiple extensions
PGCD:= proc(A,B,p)
global MEAc;
local k,Xk,minmon,least,conta,contb,c,ap,bp,g,interpol,lcinterpol,j,Aj,Bj,Cj,gj,G,lcCj,lcA,lcB,lcAk, lcBk,Randfunction,LM,lm,ring,ring2,count,XT,X,n,m,AL,BL,L,i,GCDL,deginterpol,prod, interpolj,vj,prodj,q;
#Check if A and B are in the same field
   checkconsistency(A,B);
   ring:=getring(A);
#XT is the whole variables containing the polynomial's variables and the minpolys variables
   XT:=getvars(A);
   n:=nops(XT);
   m:=nops(getalgexts(A)); 
   X:=XT[1..n-m];
   #k must be the number of polynomial variables
   k:=nops(X);
   Xk:=X[1..k-1]; #Polynomial variables= The whole variables - the variable of the minpoly
   #Base case
   if k = 1 then  
       G:=gcdrpoly(A,B);
       MEAc:=MEAc+1;
      return G;
   fi;
   #Calculate the Content/Primpart of  A and B
   conta:=contrpoly(A,Xk,'ap');
   contb:=contrpoly(B,Xk,'bp');
   #c is the gcd of the content of A and B
   c:=gcdrpoly(conta,contb);
   #g is the gcd of the leading coefficients of pp of A and B w.r.t Xk
   g:=gcdrpoly(lcrpoly(ap,Xk),lcrpoly(bp,Xk));
   lcA:=lcrpoly(ap,X);
   lcB:=lcrpoly(bp,X); 
   #q is the array of eval points. We need tracking q to avoid repetitious evaluation points
   q:=[];
   #Randfunction is the function producing the rand eval points 
   Randfunction:=rand(p);
   lcAk:=lcrpoly(ap,Xk);  
   lcBk:=lcrpoly(bp,Xk);
   #count is the counter of the acceptable eval points
   count:=0;
   while true do 
      do
         j:= Randfunction() mod p;
      until not member(j,q) and evalrpoly(lcAk,X[k]=j) mod p<>0 and evalrpoly(lcBk,X[k]=j) mod p<>0;
      Aj:=evalrpoly(ap,X[k]=j);
      Bj:=evalrpoly(bp,X[k]=j);
      Cj:=PGCD(Aj,Bj,p);
      #lm=The leading monomial of Cj
      lm:=lmrpoly(Cj,Xk,XT,p);
      #m=min(lm,n) where n=min(lm(ap),lm(bp))
      gj:=evalrpoly(g,X[k]=j);
      Cj:=scarpoly(gj,Cj);
      #To count the number of acceptable evaluation points
      if count=0 then 
         minmon:=lm;
         least:=lm;
         count:=count+1;
         deginterpol:=0;
         interpol:=Cj;
         prod:=rpoly(X[k]-j,ring);
         q := [j]; # missing !!!
      else
          least:=tmrpoly(addrpoly(lm,minmon),X,XT,p);
          if lm = least and minmon = least then 
             prodj:=evalrpoly(prod,X[k]=j);
             #print(PRODJ(prod,prodj),q,j);
             q:=[op(q),j];  #add j to q
             if count=1 then 
                interpolj:=interpol; #When count=1, interpol=Cj and Cj does not have X[k] in it so evalrpoly returns an error.
             else 
                interpolj:=evalrpoly(interpol,X[k]=j); 
             fi;   
             vj:=mulrpoly(invrpoly(prodj),subrpoly(Cj,interpolj));
             #The ring to which vj, interpol, and prod belong must be the same but at the second iteration when count=1, vj and interpol do not have y as their variable so we must reconstruct the ringto which  vj and interpol belong.
             vj:=rpoly(rpoly(vj),ring); # adding X[k]
             interpol:=rpoly(rpoly(interpol),ring);
             interpol:=addrpoly(interpol,mulrpoly(prod,vj));
             prod:=mulrpoly(prod, rpoly(X[k]-j,ring));
             deginterpol:=degrpoly(interpol,X[k]); #We did not initialize interpol since its ring changes at each iteration and it causes error. If we fixed a ring for interpol then it was more expensive than simply initialize its degree of y =0 at the first iteration
             count:=count+1;
         elif lm = least and minmon<>least then
            printf(" All the evaluation points before j=%d are unlucky",j);
             q:=[j];
             prod:=rpoly(X[k]-j,ring); # this was missing!!
             interpol:=Cj;
             minmon:= least;
             count:=1;
         elif lm<>least then  #Recognizing as an unlucky prime!
             printf("%d is an unlucky evaluation point\n",j);
         fi;
      fi;
      if  count>deginterpol+1  then   #Line 90 is equivalent to line 30 of PGCD algorithm in the paper
        G:=pprpoly(interpol,Xk);
        do
        #Make our algorithm a Monte Carlo algorithm
           L:=[seq(X[i]= Randfunction() mod p, i=2..k)];
           AL, BL, GCDL:= evalrpoly(A,L), evalrpoly(B,L), evalrpoly(G,L);
       until degrpoly(GCDL,X[1])=degrpoly(G,X[1]);
       if divrpoly(AL,GCDL) and divrpoly(BL,GCDL) then
     
       G:=mulrpoly(c,G);
          return (G);
        fi;
      fi;
   od;
end: