K<sqrt_2> := QuadraticField(-2);

r := -sqrt_2*(a^2*c + 24*a*b*c^2 - 3*sqrt_2*a + 24*b^2*c - 3*c)/(a^2 - 24*b^2 +3);
s := -1/2*sqrt_2*(a^2*c^2 + 4*a*b*c + 24*b^2*c^2 - 6*sqrt_2*b + 3*c^2)/((a^2- 24*b^2 + 3)^(1));
g := 2*(a^2*c^2 + 1/2*a^2 - sqrt_2*a*c - 24*b^2*c^2 - 12*b^2 - 12*sqrt_2*b*c^2 + 3*c^2 - 3/2)/((a^2 - 24*b^2 + 3)^(1));
h := c;

return [r,s,g,h];