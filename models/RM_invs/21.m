A1 := -1;
A := -(h-g)^2*(h^2+(24*g^3+30*g^2-26*g-30)*h-15*g^4-30*g^3+7*g^2+30*g+9)/3;
B1 := (g^4-2*h*g^3+(h^2-5/3)*g^2+10/3*h*g+(-2/3*h^2+2*h+1));
B := 2*(h-g)^4*(h^2 + (-72*g^3-63*g^2+70*g+63)*h -27*g^6-189*g^5-63*g^4+441*g^3+280*g^2-252*g-189)/27;
B2 := (g-1)^6 * (g+1)^4 * (h-g)^6;

return [A, A1, B, B1, B2];
