#LAminpoly
#Monomlist
#input: a polynomial f, a list of monomials called B, the list of variables called X
#Output:Coordinate vector of f w.r.t B
with(LinearAlgebra):
Monomlist:=proc(f,B1,X)
local m,v,i,mon,j,cof,c,d,B;
#At some examples B1 is Vector and the nops(B1) does not give the correct result so we need to convert it to list
   B:=convert(B1,list);
   d:=nops(B);
   v:=Vector(d); 
   c:=coeffs(f,X,'m');
   cof:=[c];
   mon:=[m];
   for j to nops(mon) do
      if member(mon[j],B,'i') then
         v[i]:=cof[j];
      else error "monomial not in B"
      fi;
   od;
return v;
end:
#RED
#input: a polynomial, a, the list of minimal polynomials,m, and the list of variables,X.
#output: the polynomial ,a, mod m[1],m[2],...
RED:=proc(a,m,X)
   local  a1,i;
      a1:=a;
      for i to nops(m) do
         a1:=rem(a1,m[-i],X[-i]);
      od;
      return(a1);
   end:
 #Basemaker
#input:The list of variables, the list of degree of each variable
#output: The list of all the possible monomials constructed by X mod m[i]s
Basemaker := proc(X,D::list(integer))
local x,i,M,m,Z;
if nops(X)=1 then
   x := X[1];
   seq( x^i,i=0..D[1]-1 );
else
   M := Basemaker(X[2..-1],D[2..-1]);
   x := X[1];
   Z := [seq( x^i,i=0..D[1]-1 )];
   [seq(seq( x*m, m in M ), x in Z)]
fi
end: 
LAMinpoly:=proc(m,p,gamma,X,Z)
   local n,deg,d,monombasis,g,A,B,det,q,i,j,b,M,st;
     n:=nops(m); #nops(m)=nops(X)
     deg:=[seq(degree(m[i],X[i]),i=1..n)];
     d:=mul(deg[i],i=1..n);
     monombasis:=Basemaker(X,deg,m); 
     #It is a basis for K=Z_p[z1,z2]/<z1^2-2,z2^2-3>: {1,z1,z2,z1z2}
     g[0]:=rpoly(1,getring(gamma));
     for i to d do
        g[i]:=mulrpoly(gamma,g[i-1]); 
     od;
     A:=Matrix(d);
     #Creating the matrix of coeffs
     for i from 1 to d do
         g[i-1] := expand(rpoly(g[i-1]));
         A[1..d,i]:=Monomlist(g[i-1],monombasis,X);
     od;    
     g[d] := expand(rpoly(g[d]));
     b:=Monomlist(g[d],monombasis,X);
     # Construct the augmented matrix B = [A|I|b] and row reduce it
     B:=Matrix(d,2*d+1,datatype=integer[8]);
     B[1..d,1..d] := A;
     for i to d do B[i,d+i] := 1; od;
     for i to d do B[i,2*d+1] := b[i] od;
     #Check for appropriate C here: If det(A)<>0, then A is invertible and we are good.
     #Otherwise, MGCD goes back and chooses another C   
     #if Det(A) mod p=0 then return(FAIL); fi;
     Modular:-RowReduce(p,B,d,2*d+1,2*d+1,'det',0,0,0,0,true);
     if det=0 then return FAIL fi;
     q := -B[1..d,2*d+1]; # Solve of Aq=-b for q
     B := B[1..d,d+1..2*d]; # A^(-1)
     #B:=Inverse(A) mod p;
     #q:=-B.b mod p; #As det(A)<>0 we are sure that there is a solution
     #Constructing the polynomial
     M:=add(q[i]*Z^(i-1),i=1...d)+Z^d mod p;
    return M,A,B;
end:



#phiminpoly, Phi isomorphism
#Let m=[m1(z1),m2(z2),..,mn(zn)] be the list of minimal polynomials in maple version.
#To build the ring of Q[z1,..zn]/<m1..mn> in RECDEN format,we need to present m2 as a polynomial
#over Q[z1]/<m1>, m3 as a polynomial over Q[z1,z2]/<m1,m2>,..,and m_n as a polynomial 
#over Q[z1,z2,..z_(n-1)]/<m1,m2,..,m_(n-1)>
with(ListTools):
phiminpoly:=proc(m,Xmin1) 
local n,M,i,Xmin;
   n:=nops(m);
   M:=[seq(1..n)];
   Xmin:=Reverse(Xmin1);
   M[1]:=rpoly(m[1],Xmin[n]);
   for i from 2 to n do
      Xmin[-i..n]; 
      M[i]:=phirpoly(rpoly(m[i],Xmin[-i..n]),op(M[1..i-1]));
      getring(M[i]);
od;
return(M);
end:
with(ListTools):
with(PolynomialTools):
with(ArrayTools):
with(RandomTools):
#phi : L=Q(a1,..an)---->K=Q(gamma) is an isomorhism from Q[x1,..xn]/<m1,..mn> to Q[z]/<m(z)>. If  we want to call phi, then flag:=1 else if we want to call phi^(-1) then flag:=-1 
#X is the list of minimal polynomials' variables 
#If we call phi then the minpoly of the single extension is w.r.t Z:=op(indets(M)
#If we call phi^(-1) then we need to have the variable of the single extension
#Inputs: the polynomial f1, m=[m1,..mn]=list of minimal polynomials from Q[x1,..xn]/<m1,..mn>,Xmin=minimal polynomials' variables,  Xpoly=polynomial's variables, flag=1 or -1, gama,M,A,Ainv= The out puts of LAMinpoly
Phi:=proc(f1,m,Xmin,Xpoly,flag,M,A,Ainv) 
   local n,Z,deg,d,monombasis,F,final,newf,i,basis2,f,fmin,Ringfmin,Ring,R1,R2,R3,R33,Rfinal,R, phimin,XT,Xmin1,Rf;
        #The variable of the single extension's minimal polynomial
        Z:=op(indets(M));
        Ring:=getring(f1);
        #The characteristic of the field
        R1:=op(1,Ring);
        n:=nops(m); #nops(m)=nops(X)
        deg:=[seq(degree(m[i],Xmin[i]),i=1..n)];
        d:=degree(M);   #d:=mul(deg[i],i=1..n);
        monombasis:= Basemaker(Xmin,deg); #set it as an input
        f:=expand(rpoly(f1));
        if flag=1 then #we want to calculate Phi(f) so f is in L and we need Ainv 
           R2:=[op(Xpoly),Z];
           #Get the RECDEN format of the minimal polynomial M
           fmin:=phirpoly(rpoly(1,Z),rpoly(M,[Z])); #Make the input M as RECDEN
           Ringfmin:=getring(fmin); 
           #This is the Minpoly of single extension in recden version [[],[],[]]
           R33:=[op(1,op(3,Ringfmin))];
           #The ring of single extension is Rfinal
           Rfinal:=[R1,R2,R33];
           F:= Monomlist(f,monombasis,Xmin);
           final:=Ainv.F;
           #write final as a polyomial w.r.t Z in Q[Z]/<m(Z)> 
           newf:=add(final[i]*Z^(i-1),i=1...d);
           return rpoly(newf,Rfinal); #It is costy to convert
       elif flag=-1 then #We want to call phi^(-1)
#Note: Every two bases of a vector space have the same cardinality. Hence, if the base of Q[x,y]/<m1,m2> has d items then the basis of Q[z]/<m(z)> has d items too. Remember these two vector spaces are isomorphic.
#When we call phi^(-1) we have a polynomial over Q[Z]/<m(Z)> and we want to map it to the corresponding polynomial in Q[x,y]/<m1,m2>
# write f w.r.t the basis ord:=[1,Z,Z^2,..,Z^(d-1)] of Q[Z]/<m(Z)> where deg(M(Z))=d
          basis2:=Array(1..d);
          for i to d do
             basis2[i]:=Z^(i-1); #A basis for the single extension Q[Z]/<M(Z)>
          od;
          F:=Monomlist(f,basis2,Z); #The coordinate of f relative to basis2
          final:=A.F;
          newf:=expand(RED((add(final[i]*monombasis[i],i=1..d)),m,Xmin)); #it's in Q[x,y]/<m1,m2>
          #Now, we are to construct the ring of multiple extensions
          phimin:=phiminpoly(m,Xmin);
          Xmin1:= [ seq( Xmin[-i], i=1..nops(Xmin) ) ]; #Reverse did not work here:(
          XT:=[op(Xpoly),op(Xmin1)];
          #R1; #The characteristic of the field
          if R1<>0 then #If the characteristic of the field <>0
          newf:=phirpoly(rpoly(newf,XT),op(phimin),R1);
          else #If the characteristic of the field =0
          newf:=phirpoly(rpoly(newf,XT),op(phimin));
          fi;  
          return(newf);
       fi;
end: