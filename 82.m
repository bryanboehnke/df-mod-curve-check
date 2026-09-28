/*
Showing that X_0(82) has no translates of E in W_7^1 over F_3.
*/


// Pick a prime of good reduction
p := 3;

print "Initializing curves";

P8F<a,b,c,d,e,f,g,h,i> := ProjectiveSpace(GF(p),8);
P2F<x,y,z> := ProjectiveSpace(GF(p),2);

// equations from geteqns.m
XF := Curve(P8F, [
    a^2 - a*b - b*c + b*f + e*f,
    -a*c - c^2 + a*d + a*e - a*g - c*g + d*h,
    -a*c + b*d + b*f + d*f + e*f - a*g + b*g,
    2*a*c + c*d + c*e + a*g + d*g + e*g,
    -a^2 + b*c - a*f + b*g + d*g + e*g - a*h + f*i + g*i,
    a^2 + a*e + d*f + e*f - a*g + a*h + d*h + e*h,
    a^2 + a*d + b*d + b*e + a*f + e*f + a*g + e*g - f*g - a*i - g*i,
    -b*c - a*e + a*f + b*f + f^2 - e*g + f*g + a*h + f*h + g*h + a*i + g*i,
    a^2 + c^2 - b*e + a*f + d*f + b*g + c*g + f*g + a*h - d*h + a*i - f*i,
    -a*c + a*d + a*f + d*f + e*f + e*g - f*g - g*h + a*i + f*i - g*i + h*i,
    b*d + a*e + e^2 + b*f - a*g + b*g - e*g + d*h + f*h + g*h - e*i + g*i,
    -a*c - c^2 - b*e - e^2 - d*g + d*i,
    -a^2 + a*b - a*c + d*e - a*f - a*g - d*h - d*i,
    d*e - d*f + a*g + c*g - d*g - d*h + a*i + d*i + e*i,
    -a^2 + a*b + b*d + d^2 + d*e + d*f + d*i,
    -a*c + b*c - d*g - e*g + c*i,
    -b*c + b*e + c*f - d*f - b*g,
    a*c + b*f - d*f + a*g - a*h + b*h,
    a*c - a*d - a*e - c*e + d*f + e*f + d*g + e*g - f*g + c*h - a*i + f*i,
    -a*b - b*e - a*f + b*f + b*g + c*g - e*g + f*g + g^2 - a*h - c*i,
    b^2 + c^2 + b*d + a*f + d*f + c*g + a*h + b*h + e*h + f*h + a*i + 2*b*i + 
        h*i
]);

EF := Curve(P2F, -x^3 + x*y*z + y^2*z + 2*x*z^2 + y*z^2);

phiF := map<XF -> EF | [
    -f*g + 2*f*h - 2*f*i,
    -b*g - d*g + 2*b*h + 2*d*h - g*h + 2*h^2 - 2*b*i - 2*d*i - g*i - 2*i^2,
    a*g - b*g + c*g + g^2 - c*h + e*h - g*h - a*i + c*i - 2*e*i + 2*f*i + h*i
]>;


assert Genus(XF) eq 9;
assert IsReduced(XF);
assert IsIrreducible(XF);

// Finding generator of E(F_3)
E := EllipticCurve([1, 0, 1, -2, 0]);
E := ChangeRing(E, GF(p));

assert #Points(E) eq 6;
assert Order(E![0,0,1]) eq 6;
assert IsIsomorphic(E,EF);

bool, iso := IsIsomorphic(E,EF);

P := EF![0,0,1];

assert iso(E![0,0,1]) eq P;

print "Computing pullbacks";

zero := EF![0,1,0];

Da := Pullback(phiF,Place(P));
Db := Pullback(phiF, Place(zero));
D0 := Da -Db; 
// D0 is the image of a generator on E(F_3) under  E -> J_0

print "Finding all deg 7 divisors";

// Gather all places of degree <= 7
place_list := [];
for d in [1..7] do
    deg_d := Places(XF,d);
    Append(~place_list, deg_d);
    print "- Added places of degree", d;
end for;

// find all ways to get a deg 7 divisor as sum of lower degree places
parts := Partitions(7);

// only consider divisors that can possibly move: 
// pigeonhole principle implies that any deg 7 divisor that moves must be linearly equivalent
// to a divisor with at most #X(F_p) // p+1 deg 1 places in its support
good_parts := [];
for P in parts do
    if Multiplicity(P, 1) le (#Points(XF)) div (p+1) then
        Append(~good_parts, P);
    end if;
end for;


print "Checking which deg 7 divisors move";

divs := [];

for part in good_parts do

    // for each partition of 7, 
    // consider all divisors that are sums of places of degrees equal to the parts
    deg_part := CartesianProduct([place_list[d] : d in part]);
    part;    
    total := #deg_part;
    counter:=1;

    // each element of deg_part is a tuple of places whose degrees sum to 7
    for summands in deg_part do
        
        // progress check
        if counter mod 100 eq 0 then
            printf "%o of %o divisors of type %o analyzed\n", counter, total, part;
        end if;

        // construct D as the sum of the lower degree places
        len := #summands;        
        D := 0*Divisor(summands[1]);
        for i in [1..len] do
            D := D + Divisor(summands[i]);
        end for;

        // check the dimension of L(D)
        dim := Dimension(D);
        
        // if D moves, 
        // determine if a divisor linearly equivalent to D was already added to the list
        if dim gt 1 then
            already_checked := false;
            for old_divisor in divs do
                if IsLinearlyEquivalent(D, old_divisor) then
                    already_checked := true;
                end if;
            end for;
            
            // otherwise, add D to the list
            if not already_checked then
                Append(~divs, D);
            end if;
        end if;

        counter:= counter +1;
    end for;
    print "Done";
end for;

// For each degree 7 divisor that moves, check if its translate by D0 also moves
todo := [];
for D in divs do
    dim := Dimension(D+D0); // dimension of L(D+D_0)
    if dim gt 1 then // if dimension is strictly greater than 1, then the divisor moves
        Append(~todo, D);
    end if;
end for;

print "Nr. of divisors D such that D+D0 in W_7^1:", #todo;

// For the deg 7 divisors D such that D and D+D0 move, check all translates D+i*D_0
todo2 := [];
for D in todo do
    dims := [Dimension(RiemannRochSpace(D+i*D0)) : i in [1..5]];
    if Minimum(dims) gt 1 then
        Append(~todo2, D);
    end if;
end for;

print "Nr. of divisors D such that D+i*D0 in W_7^1 for i=1,...,5:", #todo2;

assert #todo2 eq 0;

