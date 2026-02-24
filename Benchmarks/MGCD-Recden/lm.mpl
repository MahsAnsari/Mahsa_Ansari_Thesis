#Find the leading monomial of Rpoly format
#X1 is the list of variables which we do want to find lm w.r.t them i.e lm(F,[x,y],[x,y,z],p)
#Note:X1 and X are not necessarily equal
lmrpoly:=proc(F,X1,X)
local f,lc,R,M,E,Rnew,m,lm1 ;
   #switch to the simple polynomial to find its leading monomial
   #rpoly command is back and forth
   f:=rpoly(F);
   lc:=lcoeff(f,X1,'lm');
   lm1:=rpoly(lm,X);
   R:=getring(F);
   #reconstruct R
   M:=op(1,R);  
   E:=op(3,R);
   Rnew:=[M,X,E];
   m:=POLYNOMIAL(Rnew,op(2,lm1));
   return(m);
end:
#Find the smallest monomial in f
tmrpoly:=proc(F,X1,X)
local f,lc,lm1,m,R,E,Rnew,M;
    f:=rpoly2maple(op(2,F),X);
    lc:=tcoeff(f,X1,'lm');
    lm1:=rpoly(lm,X);
    R:=op(1,F);
    M:=op(1,R);
    E:=op(3,R);
    Rnew:=[M,X,E];
    m:=POLYNOMIAL(Rnew,op(2,lm1));
    return(m);
end:
#Finding the denominator of f
#If f belongs to Q[x], then the denominator of f is the smallest positive integer such that den(f)*f belongs to Z[x]
#input: a rpoly F
#output: den(F)
den:=proc(F)
    idenomrpoly(F);
end:
#Semi-Associate of f
#Semi-associate of f is defined as rf s.t r is the smallest rational for which den(f.r)=1
#Example: if f(x,y,z)=2/5*x^2+4/3*y^3+8/11*z^2 then den(f)=5*11*3 but r=den(f)/gcd(2,4,8)
semi:=proc(F)
    mulrpoly(1/icontrpoly(F),F);
end:


