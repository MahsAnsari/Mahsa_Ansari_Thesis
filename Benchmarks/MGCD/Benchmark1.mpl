
    
################################################################################################################
#takes: c=random proc, nvar=#variables, tdeg:Total degree of a,b,c, degfield= degree of the field,  
#numext= # of exts
#returns: a,b,g with total degree tdeg in recden form in a field with degree "degfield" and "numext" extentions
################################################################################################################
#Polygen Michael's dense version:
polygen:= proc(index,M,Xmin,Xpoly)
local XT,g,a,b,f1,f2,k,t,tt,tMGCD1,tMGCD2,Mahsa1,Mahsa2,T,timings,i;
XT:=[op(Xpoly), op(Xmin)];


            # Force tdeg(.,Xpoly)=d by adding a guaranteed top term Xpoly[1]^d
            g:= expand( (randpoly(Xpoly, degree=2) + Xpoly[1]^2)* (randpoly(Xmin) + 1)+ 12345/67891 );
             g := RDP:-rpoly(g, XT, M);
            a := expand( (randpoly(Xpoly, degree=2) + Xpoly[1]^2)* (randpoly(Xmin) + 1) );
            a := RDP:-rpoly(a, XT, M);
            b:= expand( (randpoly(Xpoly, degree=2) + Xpoly[1]^2)* (randpoly(Xmin) + 1) );
             b := RDP:-rpoly(b, XT, M);

timings := true;
T:=[seq(0,i=1..index)];
for k from 1 to index do
                # Convert to rpoly and reduce mod M
               
                g:=RDP:-mulrpoly(g,g);
                #a:=RDP:-mulrpoly(a,a);
                #b:=RDP:-mulrpoly(b,b);

                f1 := RDP:-mulrpoly(g, a);
                f2 := RDP:-mulrpoly(g, b);     
        
  printf("k=%d deg(f1,x1)=%d  deg(f1,x2)=%d  deg(f2,x1)=%d  deg(f2,x2)=%d  deg(g,x1)=%d  deg(g,x2)=%d\n",  k,RDP:-degrpoly(f1,x1),RDP:-degrpoly(f1,x2),RDP:-degrpoly(f2,x1),RDP:-degrpoly(f2,x2),RDP:-degrpoly(g,x1),RDP:-degrpoly(g,x2));
  t:=time():
    Mahsa1:=MGCD(f1,f2,2^31);
  tMGCD1:=time()-t;
  #P:=op(2,Mahsa1); #number of primes that were used by MGCD
  #Np:=[op(Np),P];

  tt:=time():
     Mahsa2:=MGCD2(f1,f2,2^31);
  tMGCD2:=time()-tt;
  #P:=op(2,Mahsa1); #number of primes that were used by MGCD
  #Np:=[op(Np),P];

  printf("Check=%a\n",evalb(Mahsa1=Mahsa2));
  T[k]:=tMGCD2/tMGCD1;
od:
return(T);
end proc:
