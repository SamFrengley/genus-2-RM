A1 := -4*(h+1)^2*(g-h-2)*(g-h)^3*(g+h)^4;
A := -(25*g^4+30*g^3+(-50*h^2-18*h+8)*g^2 -30*h^2*g+25*h^4+18*h^3-8*h^2+1)/3;
B1 :=  (g-h)^3*(g+h)^4 *(3*g^5-3*h*g^4-6*g^4+10*h^2*g^3+20*h*g^3+4*g^3-10*h^3*g^2-40*h^2*g^2 -44*h*g^2-8*g^2+35*h^4*g+172*h^3*g+288*h^2*g+200*h*g+52*g-35*h^5 -146*h^4-248*h^3-200*h^2-68*h-8)/3;
B := -(196*g^6+504*g^5-372*h^2*g^4-216*h*g^4+201*g^4-1008*h^2*g^3+126*g^3 +156*h^4*g^2+432*h^3*g^2-402*h^2*g^2-162*h*g^2-24*g^2+504*h^4*g -126*h^2*g+20*h^6-216*h^5+201*h^4+162*h^3+24*h^2-2)/27;
B2 := 1;

return [A, A1, B, B1, B2];