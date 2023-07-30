Fast computation of  the centralizer of a permutation group in the symmetric group

Repository containing a GAP code for computing the centralizer of a permutation group in the symmetric group based on decrease-and-conquer method.

Example:
Q := QuaternionGroup(IsPermGroup, 2^8);;
G := DirectProduct(Q, Q);;
C := FastCentralizer(G, 512);;
Computes the centralizer of the direct product of two copies of the quaternion group of order 256 in the symmetric group of degree 512.
