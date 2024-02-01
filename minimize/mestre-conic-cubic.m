/**************************************************
  SIMPLIFIED MESTRE CONIC AND CUBIC AS DEFINED IN 
  THE PAPER
**************************************************/

/**************************************************
  Mestre's conic and cubic
**************************************************/

intrinsic MestreConic(ICs::SeqEnum) -> RngMPolElt
{
  Mestre's conic in terms of IC invariants.
}
  AP, BP, CP, DP := Explode(ICs);
  Inv := IgusaClebschToClebsch(ICs);
  A, B, C, D := Explode(Inv);
  K := Parent(A);
 
  if A ne 0 then
    U := A^6;
  elif B ne 0 then
    U := B^3;
  else
    U := C^2;
  end if;

  A11 := 2*C+A*B/3;
  A22 := D;
  A33 := B*D/2+2*C*(B^2+A*C)/9;
  A23 := B*(B^2+A*C)/3+C*(2*C+A*B/3)/3;
  A31 := D;
  A12 := 2*(B^2+A*C)/3;
  A32 := A23;  A13 := A31;  A21 := A12;

  C11 := A11*U^2/DP^3;
  C22 := A22/DP^1;
  C33 := A33*U^8/DP^11;
  C23 := A23*U^4/DP^6;
  C31 := A31*U^5/DP^7;
  C12 := A12*U/DP^2;
  C32 := C23;  C13 := C31;  C21 := C12;

  PP<X1,X2,X3> := PolynomialRing(K,3);
  L := C11*X1^2+C22*X2^2+C33*X3^2+2*C12*X1*X2+2*C13*X1*X3+2*C23*X2*X3;

  return L;
end intrinsic;


intrinsic MestreCubic(ICs::SeqEnum) -> RngMPolElt
{
  Mestre's cubic in terms of IC invariants.
}
  AP, BP, CP, DP := Explode(ICs);
  Inv := IgusaClebschToClebsch(ICs);
  A, B, C, D := Explode(Inv);

  K := Parent(A);
 
  if A ne 0 then
    U := A^6;
  elif B ne 0 then
    U := B^3;
  else
    U := C^2;
  end if;

  a111 := 8*(A^2*C-6*B*C+9*D)/36 ;
  a112 := 4*(2*B^3+4*A*B*C+12*C^2+3*A*D)/36 ;
  a113 := 4*(A*B^3+4*A^2*B*C/3+4*B^2*C+6*A*C^2+3*B*D)/36 ;
  a122 := a113;
  a123 := 2*(2*B^4+4*A*B^2*C+4*A^2*C^2/3+4*B*C^2+3*A*B*D+12*C*D)/36 ;
  a133 := 2*(A*B^4+4*A^2*B^2*C/3+16*B^3*C/3+26*A*B*C^2/3+
             8*C^3+3*B^2*D+2*A*C*D)/36 ;
  a222 := 4*(3*B^4+6*A*B^2*C+8*A^2*C^2/3+2*B*C^2-3*C*D)/36 ;
  a223 := 2*(-2*B^3*C/3-4*A*B*C^2/3-4*C^3+9*B^2*D+8*A*C*D)/36 ;
  a233 := 2*(B^5+2*A*B^3*C+8*A^2*B*C^2/9+2*B^2*C^2/3
                                         -B*C*D+9*D^2)/36 ;
  a333 := 1*(-2*B^4*C-4*A*B^2*C^2-16*A^2*C^3/9-4*B*C^3/3
             +9*B^3*D+12*A*B*C*D+20*C^2*D)/36 ;
  P := U^(-18)*DP^5 ;

  c111 := a111*P*U^3*DP^12 ;
  c112 := a112*P*U^2*DP^13 ;
  c113 := a113*P*U^6*DP^8 ;
  c122 := a122*P*U*DP^14 ;
  c123 := a123*P*U^5*DP^9 ;
  c133 := a133*P*U^9*DP^4 ;
  c222 := a222*P*DP^15 ;
  c223 := a223*P*U^4*DP^10 ;
  c233 := a233*P*U^8*DP^5 ;
  c333 := a333*P*U^12 ;

  PP<X1,X2,X3> := PolynomialRing(K,3);

  M := c111*X1^3+c222*X2^3+c333*X3^3+3*c112*X1^2*X2+3*c113*X1^2*X3+
       3*c122*X1*X2^2+3*c133*X1*X3^2+3*c233*X2*X3^2+3*c223*X2^2*X3+
       6*c123*X1*X2*X3;

  return M;
end intrinsic;


intrinsic MestreConicCubic(ICs::SeqEnum) -> RngMPolElt, RngMPolElt
{
  Mestre's conic and cubic in terms of the IC invariants.
}
  R := Parent(ICs[1]);
  S<x1,x2,x3> := PolynomialRing(R,3);

  L := S!(MestreConic(ICs));
  M := S!(MestreCubic(ICs));
  return L, M;
end intrinsic;


/**************************************************
  IC simplified forms
**************************************************/

intrinsic ICConic(ICs::SeqEnum) -> RngMPolElt
{
  Simplified conic in terms of the IC invariants, presented in Section 4.1.
}
  I2,I4,I6,I10 := Explode(ICs);
  
  M := Matrix([[-3*I2^3 - 140*I2*I4 + 800*I6, 7*I2^2*I4 + 80*I4^2 - 30*I2*I6, -230*I2*I4^2 - 9*I2^2*I6 + 1040*I4*I6 + 108000*I10],
 [7*I2^2*I4 + 80*I4^2 - 30*I2*I6, 117*I2*I4^2 - 360*I4*I6 - 81000*I10, -50*I2^2*I4^2 + 20*I4^3 + 321*I2*I4*I6 - 540*I6^2 + 24300*I2*I10],
 [-230*I2*I4^2 - 9*I2^2*I6 + 1040*I4*I6 + 108000*I10, -50*I2^2*I4^2 + 20*I4^3 + 321*I2*I4*I6 - 540*I6^2 + 24300*I2*I10, -200*I2*I4^3 + 920*I4^2*I6 - 27*I2*I6^2 + 102600*I4*I10]]);
 return DefiningPolynomial(Conic(M));
end intrinsic;


intrinsic ICCubic(ICs::SeqEnum) -> RngMPolElt
{
  Simplified cubic in terms of the IC invariants, presented in Section 4.1.
}
  I2,I4,I6,I10 := Explode(ICs);
  R := Parent(I2);
  S<x1,x2,x3> := PolynomialRing(R,3);
  
  a111 := (-1/90) * (27*I2^5 + 2000*I2^3*I4 - 41600*I2*I4^2 - 11400*I2^2*I6 + 192000*I4*I6 + 28800000*I10);
  a112 := (-1/30) * (-63*I2^4*I4 - 7780*I2^2*I4^2 + 270*I2^3*I6 - 3200*I4^3 + 67200*I2*I4*I6 - 144000*I6^2 + 1620000*I2*I10);
  a113 := (-1/10) * (-310*I2^3*I4^2 + 27*I2^4*I6 - 9200*I2*I4^3 + 3620*I2^2*I4*I6 + 44800*I4^2*I6 - 13200*I2*I6^2 + 162000*I2^2*I10 + 5280000*I4*I10);
  a122 := (-1/10) * (-I2^3*I4^2 - 620*I2*I4^3 + 330*I2^2*I4*I6 - 900*I2*I6^2 + 1080000*I4*I10);
  a123 := (1/15) * (225*I2^4*I4^2 + 8155*I2^2*I4^3 - 1161*I2^3*I4*I6 + 800*I4^4 - 75120*I2*I4^2*I6 + 1215*I2^2*I6^2 - 109350*I2^3*I10 + 165600*I4*I6^2 - 3969000*I2*I4*I10 + 19440000*I6*I10);
  a133 := (-1/30) * (-650*I2^3*I4^3 - 18700*I2*I4^4 + 270*I2^2*I4^2*I6 + 243*I2^3*I6^2 + 91200*I4^3*I6 + 33660*I2*I4*I6^2 + 340200*I2^2*I4*I10 - 129600*I6^3 + 10008000*I4^2*I10 + 1458000*I2*I6*I10);
  a222 := (9/10) * (53*I2^2*I4^3 + 40*I4^4 - 360*I2*I4^2*I6 + 600*I4*I6^2 - 30000*I2*I4*I10 + 90000*I6*I10);
  a223 := (-1/10) * (350*I2^3*I4^3 + 1540*I2*I4^4 - 3603*I2^2*I4^2*I6 - 6840*I4^3*I6 + 13140*I2*I4*I6^2 - 170100*I2^2*I4*I10 - 16200*I6^3 - 702000*I4^2*I10 + 729000*I2*I6*I10);
  a233 := (1/30) * (14650*I2^2*I4^4 + 1350*I2^3*I4^2*I6 + 200*I4^5 - 121920*I2*I4^3*I6 - 7533*I2^2*I4*I6^2 + 248760*I4^2*I6^2 + 9720*I2*I6^3 - 15163200*I2*I4^2*I10 - 656100*I2^2*I6*I10 + 63666000*I4*I6*I10 + 3936600000*I10^2);
  a333 := (-1/90) * (5000*I2^3*I4^4 - 9500*I2*I4^5 - 65850*I2^2*I4^3*I6 + 46200*I4^4*I6 + 297540*I2*I4^2*I6^2 + 729*I2^2*I6^3 - 4860000*I2^2*I4^2*I10 - 476280*I4*I6^3 + 4986000*I4^3*I10 + 32221800*I2*I4*I6*I10 - 43740000*I6^2*I10 + 1180980000*I2*I10^2);
  return a111*x1^3 + a112*x1^2*x2 + a113*x1^2*x3 + a122*x1*x2^2 + a123*x1*x2*x3 + a133*x1*x3^2 + a222*x2^3 + a223*x2^2*x3 + a233*x2*x3^2 + a333*x3^3;
end intrinsic;


intrinsic ICConicCubic(ICs::SeqEnum) -> RngMPolElt, RngMPolElt
{
  Simplified conic and cubic in terms of the IC invariants, presented in Section 4.1.
}
  R := Parent(ICs[1]);
  S<x1,x2,x3> := PolynomialRing(R,3);

  L := S!(ICConic(ICs));
  M := S!(ICCubic(ICs));
  return L, M;
end intrinsic;


/**************************************************
  RM simplified forms
**************************************************/

intrinsic RMConic(AA::SeqEnum) -> RngMPolElt
{
  Simplified conic in terms of the RM invariants, presented in Section 4.2.
}
  A,A1,B,B1,B2 := Explode(AA);
  
  A11 := -225/2*A1^3*B + 285/2*A*A1^2*B1 + 162*B1^3;
  A12 := 10*A^2*A1^2 - 45/2*A1*B*B1 + 18*A*B1^2;
  A13 := 45*A*A1^2*B + 15*A^2*A1*B1 - 375/2*A1^3*B2 + 81*B*B1^2;
  A22 := -30*A*A1*B + 2*A^2*B1 + 125/2*A1^2*B2;
  A23 := 10*A^3*A1 - 135/2*A1*B^2 + 9*A*B*B1 + 225*A1*B1*B2;
  A33 := 90*A^2*A1*B - 525/2*A*A1^2*B2 + 81/2*B^2*B1;
  M := Matrix([[A11,A12,A13], [A12, A22, A23], [A13, A23, A33]]);
  return DefiningPolynomial(Conic(M));
end intrinsic;


intrinsic RMCubic(AA::SeqEnum) -> RngMPolElt
{
  Simplified cubic in terms of the RM invariants, presented in Section 4.2.
}
  A,A1,B,B1,B2 := Explode(AA);
  R := Parent(A);
  S<x0,x1,x2> := ProjectiveSpace(R,2);
  
  return (2500*A1^6*B2 - 1800*A1^5*A*B + 1680*A1^4*A^2*B1 - 5130*A1^3*B1^2*B + 6480*A1^2*A*B1^3 + 23328/5*B1^5)*x0^3 + (-80*A1^4*A^3 - 2250*A1^4*B1*B2 + 2700*A1^4*B^2 - 4320*A1^3*A*B1*B + 1656*A1^2*A^2*B1^2 - 1944*A1*B1^3*B + 7776/5*A*B1^4)*x0^2*x1 + (-500*A1^4*A*B2 + 248*A1^2*A^3*B1 - 270*A1^2*B1*B^2 + 648*A1*A*B1^2*B + 864/5*A^2*B1^3)*x0*x1^2 + (250*A1^3*B*B2 + 16*A1^2*A^4 - 180*A1^2*A*B^2 + 96*A1*A^2*B1*B + 32/5*A^3*B1^2)*x1^3 + (4500*A1^5*A*B2 - 2160*A1^4*A^2*B + 1560*A1^3*A^3*B1 + 8100*A1^3*B1^2*B2 - 8910*A1^3*B1*B^2 + 7452*A1^2*A*B1^2*B + 1296*A1*A^2*B1^3 + 34992/5*B1^4*B)*x0^2*x2 + (9000*A1^4*B*B2 - 160*A1^3*A^4 - 15300*A1^3*A*B1*B2 - 1080*A1^3*A*B^2 + 2592*A1^2*A^2*B1*B - 432*A1*A^3*B1^2 - 19440*A1*B1^3*B2 + 2916*A1*B1^2*B^2 + 7776/5*A*B1^3*B)*x0*x1*x2 + (-1100*A1^3*A^2*B2 + 456*A1^2*A^3*B + 2700*A1^2*B1*B*B2 - 810*A1^2*B^3 - 64*A1*A^4*B1 - 2160*A1*A*B1^2*B2 + 864*A1*A*B1*B^2 + 432/5*A^2*B1^2*B)*x1^2*x2 + (3300*A1^4*A^2*B2 - 720*A1^3*A^3*B + 4050*A1^3*B1*B*B2 - 4860*A1^3*B^3 - 120*A1^2*A^4*B1 + 3240*A1^2*A*B1^2*B2 + 5022*A1^2*A*B1*B^2 - 1944*A1*A^2*B1^2*B + 17496/5*B1^3*B^2)*x0*x2^2 + (11250*A1^4*B2^2 - 7650*A1^3*A*B*B2 - 80*A1^2*A^5 - 1440*A1^2*A^2*B1*B2 + 2052*A1^2*A^2*B^2 - 576*A1*A^3*B1*B - 9720*A1*B1^2*B*B2 + 1944*A1*B1*B^3 + 1944/5*A*B1^2*B^2)*x1*x2^2 + (1300*A1^3*A^3*B2 + 13500*A1^3*B1*B2^2 - 6750*A1^3*B^2*B2 - 360*A1^2*A^4*B + 1620*A1^2*A*B1*B*B2 + 1458*A1^2*A*B^3 - 1296*A1*A^2*B1*B^2 + 2916/5*B1^2*B^3)*x2^3;
end intrinsic;


intrinsic RMConicCubic(AA::SeqEnum) -> RngMPolElt, RngMPolElt
{
  Simplified conic and cubic in terms of the RM invariants, presented in Section 4.2.
}
  L := RMConic(AA);
  M := RMCubic(AA);
  M := Parent(L)!M;

  return L, M;
end intrinsic;
