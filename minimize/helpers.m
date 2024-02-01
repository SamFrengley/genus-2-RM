/*
  Some helpful abbreviation functions
*/


intrinsic SingularSS(S::Sch) -> SeqEnum
{Return the irreducible components of the singular subscheme of S
but without scheme structure.}
  return IrreducibleComponents(ReducedSubscheme(SingularSubscheme(S)));
end intrinsic;

intrinsic FactNum(f::Any) -> SeqEnum
{Factorise the numerator of f}
  return Factorisation(Numerator(f));
end intrinsic;


intrinsic FactDen(f::Any) -> SeqEnum
{Factorise the denominator of f}
  return Factorisation(Denominator(f));
end intrinsic;


/**************************************************
  Evaluate a polynomial over polynomial ring
**************************************************/

intrinsic NewCoeffs(f::Any, ev::SeqEnum) -> Any
{
Given a polynomial f  \in k(t_1,...,t_k)[x_1,...,x_n] return the coeffs and mons of the
polynomial given by evaluating [t_i] at "ev".
}
  ms := Monomials(f);
  cc := Coefficients(f);
  cc2 := [];

  for i in [1..#cc] do
    Append(~cc2, Evaluate(cc[i], ev));
  end for;

  return cc2, ms;
end intrinsic;

intrinsic EvaluateCoefficients(f::Any, ev::SeqEnum) -> Any
{
Given a polynomial f \in k(t_1,...,t_k)[x_1,...,x_n] return the polynomial given by
evaluating [t_i] at "ev"
}
  cc, ms := NewCoeffs(f, ev);
  return &+[cc[i]*ms[i] : i in [1..#ms]];
end intrinsic;

                                                         
intrinsic EvaluateCoefficientsAndVars(f::Any, ev::SeqEnum, xy::SeqEnum) -> Any
{
Given a polynomial f \in k(t_1,...,t_k)[x_1,...,x_n] return the polynomial given by
evaluating [t_i] at "ev" and evaluating [x_i] at "xy"
}
  cc, ms := NewCoeffs(f, ev);
  new_f := 0;
  for i in [1..#cc] do
    new_f := new_f + Evaluate(ms[i], xy)*cc[i];
  end for;
  return Numerator(new_f);
end intrinsic;


/**************************************************
Clear the denominators and rescale a polynomial
**************************************************/
intrinsic ClearDens(L::Any) -> Any
{
Given a polynomial f \in k(t_1,...,t_k)[x_1,...,x_n] return the polynomial given by 
(1) clearing denominators of the coeffs of f
(2) dividing by common factors of the coeffs of f
}
  cc := Coefficients(L);
  d := LCM([Denominator(c) : c in cc]);
  n := GCD([Numerator(c) : c in cc]);
  L := d/n * L;

  cc := Coefficients(L);
  cc := &cat [Coefficients(Numerator(c)) : c in cc];
  n := GCD([Numerator(c) : c in cc]);
  d := LCM([Denominator(c) : c in cc]);

  L := d/n * L;
  return L;
end intrinsic;

