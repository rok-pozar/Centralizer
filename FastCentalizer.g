LoadPackage("datastructures");

#
# treeParent - List of parents of a Schreier tree, where treeParent[i] is the parent of i,
#                     that is, there is an arc from treeParent[i] to i in the Schreier tree
# treeLabel   - List of labels, where treeLabel[i] is the label of the arc from treeParent[i] to i 
# u                - tree vertex
#
# This function traces the Schreier tree given by treeParent and treeLabel and 
# returns and returns a word in the generators that maps the root to u. 


BindGlobal( "TraceTree",
function(treeParent, treeLabel, u)
	local k, word;
	k := treeLabel[u];
	word := [];
	while k <> -1 do
		Add(word, k);
		u := treeParent[u];
		k :=  treeLabel[u];
	od;
	return Reversed(word);
end);


#
# w - List of positive integers less than or equal to d  
# d  - number of all generators (labels)
#
# This function returns the inverse word of w, where
# for  i < Int(d/2) + 1, the indices i and (i + Int(d/2)) correspond to inverse permutations.
# 

BindGlobal( "inverseWord",
function(w, d)
	local s, i;
	d := Int(d/2);
	s := [];
	for i in w do
		if i < d+1 then
			Add(s, i + d);
		else
			Add(s, i - d);
		fi;
	od;
	return Reversed(s);
end);

#
# V          - List of points from {1, 2, ..., n}
# T	       - List of permutations on {1, 2, ..., n} 
# kappa   - List of indices from {1, 2, ..., d} corresponding to permutation word
#
# This function returns the partition of V into C and O such that 
# V[i] belongs to C if and only if the permutation T[kappa[1]]*T[kappa[2]]*...*T[kappa[r]] fixes V[i].
# 

BindGlobal( "partition",
function(V, T, kappa)
	local i, j, P, O, C, a, im;
	O := [];
	C := [];
	for i in V do
		im := i;
		for j in kappa do
			a := T[j];
			im := im^a;
		od;
		if im = i then
			Add(C, i);
		else
			Add(O, i);
		fi;
	od;
	return [O, C];
end);



#
# FIFO queue
# A[1] is the index of the first element
# A[2] is the index of the last element 


BindGlobal( "FIFOnew",
function(n)
	local A;
	A := List([1..n+2], x -> 0);
	A[1] := 3;
	A[2] := 2;
	return A;
end);

BindGlobal( "FIFOempty",
function(A)
	if A[1] >  A[2] then
		return true;
	else
		return false;
	fi;
end);

BindGlobal( "FIFOenqueue",
function(A, elt)
	A[A[2] + 1] := elt;
	A[2] := A[2] + 1;
end);


BindGlobal( "FIFOdequeue",
function(A)
	local elt;
	elt := A[A[1]];
	A[1] := A[1] + 1;
	return elt;
end);



#
# T1        - List of group generators acting  transitively on {1, 2, ..., n} 
# T2        - List of group generators acting  transitively on {1, 2, ..., n} 
# alpha   - point in {1, 2, ..., n} 
# beta     - point in {1, 2, ..., n} 
# n          - degree
#
#
# This function returns an equivalence phi between the actions T1 and T2, respectively, 
# with phi(alpha) = beta, if such one exists, and otherwise a discriminant permutation word for alpha and beta.
# If T1 = T2, this function returns the centralizer element c in C_{S_n}(<T1>) with alpha^c = \beta, if such one exists, 
# and otherwise a discriminant permutation word for alpha and beta.
# We assume that Ti = [x_1, x_2,..., x_d, x_1^-1, x_2^-1,..., x_d^-1]
# 

BindGlobal( "Fixed",
function(T1, T2, alpha, beta, n)
	local  i, d, phi, Q, x1, x2, u, T1Label, T2Label, T1Parent, T2Parent, word, k, r;
	d:=Length(T1);
	phi := List([1..n], x -> 0); 
	phi[alpha] := beta;                                                        #potential equivalence mapping alpha to beta
	T1Parent := List([1..n], x -> 0); 
	T1Parent[alpha] := -1;                                                  
	T1Label := List([1..n], x -> 0); 
	T1Label[alpha] := -1; 						#Schreier tree for T1 with root alpha
	T2Parent := List([1..n], x -> 0); 
	T2Parent[beta] := -1;	 
	T2Label := List([1..n], x -> 0); 
	T2Label[beta] := -1;							#Schreier tree for T2 with root beta
	Q := FIFOnew(n);
	FIFOenqueue(Q, alpha);	
	while not FIFOempty(Q) do
		u := FIFOdequeue(Q);
		for i in [1..d] do
			x1 := T1[i]; 
			x2 := T2[i];
			if T1Label[u^x1] <> 0 then                                  #a cotree arc in Schreier tree for T1
				if  (phi[u])^x2 <> phi[u^x1]  then                 # a discrimination word closed in Schreier digraph for T1
					r := TraceTree(T1Parent, T1Label, u);
					Add(r, i);
					word := Concatenation(r, inverseWord(TraceTree(T1Parent, T1Label, u^x1),d));
					return [0, word];
				fi;
			else                                                                     #a tree arc in Schreier tree for T1
				if phi[u^x1] > 0 then                                    #a discrimination word closed in Schreier digraph for T2	
					r := TraceTree(T2Parent, T2Label, phi[u]);
					Add(r, T2Label[phi[u^x1]]);
					word := Concatenation(r, inverseWord(TraceTree(T2Parent, T2Label, phi[u^x1]),d));
					return [0, word];
				else                                                              # expand the map
					FIFOenqueue(Q, u^x1);
					phi[u^x1] := (phi[u])^x2; 
					T1Parent[u^x1] := u; 
					T2Parent[(phi[u])^x2] := phi[u]; 
					T1Label[u^x1] := i;	
					T2Label[(phi[u])^x2] := i;	
				fi;		
			fi;		
		od;	
	od;
	return [1, phi];
end);



#
# T        - List of group generators acting transitively on {1, 2, ..., n} 
# n        - degree
#
#
# This function returns a list of generators of the centralizer of the group generated by T in the symmetric group of degree n.
# 


BindGlobal( "TransitiveCentralizer",
function(T, n)
	local R, Tstar, C, alpha, beta, check, gen, r, reduce, P, newR;
	
	C := PartitionDS( IsPartitionDSRep , n );
	R := [1..n];
	gen := [];
	Tstar := Concatenation(T, List(T, a -> a^-1));
	while Size(R) > 1 do
		alpha := R[1];
		beta := R[2];  
		check := Fixed(Tstar, Tstar, alpha, beta, n);
		if check[1] = 1 then
			Add(gen, PermList(check[2]));
			newR := [];
			for r in R do
				if Representative(C, r) <> Representative(C, check[2][r]) then
					Unite(C, r, check[2][r]);
				else 
					Add(newR, r);
				fi;	
			od;
			R := newR;
		else	
			P := partition(R, Tstar, check[2]);
			if  Size(P[1]) < Size(P[2]) then
				R := P[1];
			else
				R := P[2];
			fi;	
		fi;
	od;
	return gen;
end);




#
# T1        - List of group generators acting  transitively on {1, 2, ..., n} 
# T2        - List of group generators acting  transitively on {1, 2, ..., n} 
# n          - degree
#
# This function tests whether two transitive actions T1 and T2 on {1, 2, ..., n}  are equivalent.
# 

BindGlobal( "TransitiveEquivalence",
function(T1, T2, n)
	local V1, V2, v, w, P1, P2, kappa, T1star, T2star;
	V1 :=  [1..n];
	V2 :=  [1..n];
	T1star := Concatenation(T1, List(T1, a -> a^-1));
	T2star := Concatenation(T2, List(T2, a -> a^-1));
	repeat 
		v := V1[1];
		w := V2[1];
		kappa := Fixed(T1star, T2star, v, w, n);
		if kappa[1] <> 1 then
			P1 := partition(V1, T1star, kappa[2]);
			P2 := partition(V2, T2star, kappa[2]);
			if  Size(P1[1]) < Size(P1[2]) then
				V1 := P1[1];
				V2 := P2[1];
			else
				V1 := P1[2];
				V2 := P2[2];
			fi;			
		fi;	
	until ((kappa[1] = 1) or Size(V1) <> Size(V2));
	if kappa[1] = 1 then 
		return kappa[2];
	else
		return [];
	fi;
end);

##########################################################
##                                     Main function
##########################################################
#
# G        - Permutation group acting on {1, 2, ..., n} 
# n        - degree
#
#
# This function returns the centralizer of the group G in the symmetric group of degree n.
# 


BindGlobal( "FastCentralizer",
function(G, n)

	local T, gen, L, orbits, C, i, relabel, o, j, r, ki, kj, orbi, orbj, Crel, Ti, gr, img, conv, l, Tj, phi, Tr, g;
	
	T := GeneratorsOfGroup(G);
	orbits := OrbitsPerms( T, [ 1 .. n ] );
	r := Size(orbits); 
	L := List([1..r], x -> 0);
	
	relabel := [];
	for o in orbits do
		for j in [1..Size(o)] do
			relabel[o[j]] := j;
		od;
	od;
	
	# for each orbit O compute the restriction of G to O as a permutation group acting on {1, 2, ..., |O|}	
	Tr := List([1..r], x -> 0);
	for i in [1..r] do
		o := orbits[i];
		ki := Size(o);
			Ti := [];
			for g in T do
				gr := List([1..ki], x -> 0);
				for l in [1..ki] do
					img := relabel[o[l]^g];
					gr[l] := img;
				od;
				Add(Ti, PermList(gr));
			od;
		Tr[i] := Ti;
	od;
	
	gen := [];
	for i in List([1..r], x -> r - x +1) do
		orbi := orbits[i];
		ki := Size(orbi);
		Ti := Tr[i];
		if L[i] = 0 then
			C:= TransitiveCentralizer(Ti, ki);
			if C <> [] then
				# relabel into original labels
				Crel := [];
				for g in C do
					conv := List([1..n], x -> x);
					for j in [1..ki] do
						conv[orbi[j]] := orbi[j^g]; 
					od;
					Add(Crel, PermList(conv));
				od;
				Append(gen, Crel);
			fi;
		fi;	
		for j in List([1..(i -1)], x -> i - x) do
			orbj := orbits[j];
			kj := Size(orbj);
			if kj = ki then
				Tj := Tr[j];
				phi := TransitiveEquivalence(Ti, Tj, ki);
				if phi <> [] then
				# relabel into original labels and
				# interchange Ti and Tj (that is, both orbits) and leave fixed outside 
					conv := List([1..n], x -> x);
					for l in [1..ki] do
						conv[orbi[l]] := orbj[phi[l]]; 
						conv[orbj[phi[l]]] := orbi[l];
					od;
					Add(gen, PermList(conv));
					L[j] := 1;
					break;
				fi;			
			fi;
		od;
	
	od;
	if gen = [] then
		return Group(());
	else
		return Group(gen);
	fi;
end);
