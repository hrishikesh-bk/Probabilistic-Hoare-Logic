# Probabilistic-Hoare-Logic

A formalization of logic TPHL from research paper 'A Complete Truth-functional Probabilistic Hoare Logic' submitted to POPL26, along with proofs of example propbabilistic programs as discussed in the paper.

The formalization is implemented in Rocq Theorem prover. The code was tested on Rocq-version 8.19.2. 

File PHLTest contains the formalisation of TPHL along with small illustrative examples.
To run the code, first compile PHLTest.v followed by Uniform.v (EscapingSpline.v and RandomWalk.v depend on Uniform.v). 
Now you can step through any of the files. In our test, all files were proved completely.

References:
Maps.v is taken from the Software Foundations book (https://softwarefoundations.cis.upenn.edu). Required as a dependency in PHLTest.v. 
