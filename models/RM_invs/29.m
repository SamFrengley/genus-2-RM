A1 := 8*h^2*g^2*(g-4*h)^2;
A := -(9*g^2+72*h*g-54*g+16*h^2-8*h+1)/3;
B1 := -2*g^2*(3*g^4-36*h*g^3+48*h^4*g^2-16*h^3*g^2+148*h^2*g^2-64*h^4*g -224*h^3*g+512*h^5+64*h^4)/3;
B := -2*(108*h^2*g^2-162*h*g^2+405*g^2-648*h^2*g+648*h*g-135*g+64*h^3 -48*h^2+12*h-1)/27;
B2 := -1/2;

return [A, A1, B, B1, B2];