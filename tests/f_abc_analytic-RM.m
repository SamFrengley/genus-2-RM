/**************************************************
Sanity checking the equations f_D(a,b,c; x);
**************************************************/

AttachSpec("../models/spec");
CC := ComplexField(500);
PP<x> := PolynomialRing(CC);

//DISCRIMINANTS := [5, 8, 12, 13, 17];
DISCRIMINANTS := [8, 12, 13, 17];

print "====================================";
print "TEST: Random choices of a,b,c";
print "====================================";

for D in DISCRIMINANTS do
  a,b,c := Explode([Random(-100, 100)/Random(1,50) : i in [1..3]]);

  if D eq 17 then
    abc := [a,b];
  else
    abc := [a,b,c];
  end if;
  
  f := RMWeierstrassEquationRational(D, abc);
  A := AnalyticJacobian(PP!f);
  E := EndomorphismAlgebra(A);

  min_plys := [MinimalPolynomial(g) : g in Generators(E)];
  flag := exists{m : m in min_plys | Discriminant(m) eq D};
  printf "The test for D=%o is %o\n", D, flag;
end for;


/**************************************************
Sanity checking the equations f_D(a,b,c,z; x);
**************************************************/

print "\n====================================";
print "NON-RATIONAL CASES";
print "TEST: Random choices of a,b,c";
print "====================================";

DISCRIMINANTS := [21, 28, 29, 37, 44, 53, 61];

for D in DISCRIMINANTS do
  a,b,c := Explode([Random(-100, 100)/Random(1,50) : i in [1..3]]);

  Lambda := GetUpperLambda_D(D : coords:=[a,b,c]);
  zeta := Roots(x^2 - Lambda)[1][1];

  f := RMWeierstrassEquationLambda(D, zeta, a, b, c);
  A := AnalyticJacobian(PP!f);
  E := EndomorphismAlgebra(A);

  min_plys := [MinimalPolynomial(g) : g in Generators(E)];
  flag := exists{m : m in min_plys | Discriminant(m) eq D};
  printf "The test for D=%o is %o\n", D, flag;
end for;
