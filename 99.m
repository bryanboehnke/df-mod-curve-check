/*
Showing that X_0(99) has no translates of E in W_7^1 over F_2
*/


// Pick a prime of good reduction
p := 2;

print "Initializing curves";

P8F<a,b,c,d,e,f,g,h,i> := ProjectiveSpace(GF(p),8);
P2F<x,y,z> := ProjectiveSpace(GF(p),2);

// equations from geteqns.m
XF := Curve(P8F, [
    f^2 + g*h,
    -a*f + b*g,
    -a^2 - a*f + c*g,
    b*f + a*h,
    -a*b + c*f + a*h,
    -b^2 + b*h - c*h,
    -b*e + a*f + b*g + d*h,
    a*c + b*f + d*g - a*h,
    a*e + d*f - 2*a*g,
    -a*d + a*e + 2*e*f - a*g + g*i,
    -b*d + b*e - a*f - 2*e*h + f*i,
    a*c + d*e - c*f - d*g + a*h - b*i,
    -a^2 + b*d - b*e + c*e + a*f - c*g,
    c*d - b*e - a*f - c*g - d*h - a*i,
    b^2 + c^2 + a*d + d*f - b*h - c*h,
    b^2 - b*c - d*f + b*h + c*h,
    a*b - e^2 + c*f + 2*e*g + h*i,
    c*f - e*g + 2*g^2 - 2*f*h,
    2*a*b + a*c + d^2 + c*f + a*h - b*i + c*i,
    e*f - 2*f*g + c*h - 2*h^2,
    b^2 + d*f + 2*e*f + a*g + f*g + b*h + c*h + h^2 + 
        e*i - g*i
]);

EF := Curve(P2F, y^2*z +x*y*z+y*z^2-x^3+x^2*z+2*x*z^2
);

phiF := map<XF -> EF | [
    -c - e + f + 2*g + h,
    a + b + c + d,
    b + e - f - 2*g - h
]>;


assert Genus(XF) eq 9;
assert IsReduced(XF);
assert IsIrreducible(XF);

// Finding generator of E(F_2)
E := EllipticCurve([1, -1, 1, -2, 0]);
E := ChangeRing(E, GF(p));


assert #Points(E) eq 4;
assert Order(E![0,0,1]) eq 4;
assert IsIsomorphic(E,EF);

bool, iso := IsIsomorphic(E,EF);

P := EF![0,0,1];

assert iso(E![0,0,1]) eq P;

print "Computing pullbacks";

zero := EF![0,1,0];

Da := Pullback(phiF,Place(P));
Db := Pullback(phiF, Place(zero));
D0 := Da -Db;
// D0 is the image of a generator on E(F_2) under  E -> J_0


print "Finding all deg 7 divisors";

// Get all places of degree <= 7
place_list := [];
for d in [1..7] do
    deg_d := Places(XF,d);
    Append(~place_list, deg_d);
    print "- Added places of degree", d;
end for;

// find all ways to get a deg 7 divisor as sum of lower degree places
parts := Partitions(7);

// only consider ones that can possibly move: 
// pigeonhole principle implies that any deg 7 divisor that moves must be linearly equivalent
// to a divisor with at most #X(F_p) // p+1 deg 1 places in its support
good_parts := [];
for P in parts do
    if Multiplicity(P, 1) le (#Points(XF)) div (p+1) then
        Append(~good_parts, P);
    end if;
end for;


print "Checking which deg 7 divisors move.";

divs := [];

for part in good_parts do

    // for each partition of 7, 
    // consider all divisors that are sums of places of degrees equal to the parts
    deg_part := CartesianProduct([place_list[d] : d in part]);
    type := part;    
    total := #deg_part;
    counter:=1;

    // each element of deg_part is a tuple of places whose degrees sum to 7
    for summands in deg_part do

        // progress check
        if counter mod 100 eq 0 then
            printf "%o of %o divisors of type %o analyzed\r", counter, total, type;
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
    dim := Dimension(RiemannRochSpace(D+D0)); // dimension of L(D+D_0)
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
