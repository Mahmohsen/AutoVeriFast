[![Build Status](https://travis-ci.org/verifast/verifast.svg?branch=master)](https://travis-ci.org/verifast/verifast) [![Build status](https://ci.appveyor.com/api/projects/status/1w7vchky3k6erltw?svg=true)](https://ci.appveyor.com/project/verifast/verifast)

 
VeriFast
========

By Bart Jacobs\*, Jan Smans\*, and Frank Piessens\*, with contributions by Pieter Agten\*, Cedric Cuypers\*, Lieven Desmet\*, Jan Tobias Muehlberg\*, Willem Penninckx\*, Pieter Philippaerts\*, Amin Timany\*, Thomas Van Eyck\*, Gijs Vanspauwen\*,  Frédéric Vogels\*, and [external contributors](https://github.com/verifast/verifast/graphs/contributors)

\* imec-DistriNet research group, Department of Computer Science, KU Leuven - University of Leuven, Belgium

VeriFast is a research prototype of a tool for modular formal verification of correctness properties of single-threaded and multithreaded C and Java programs annotated with preconditions and postconditions written in separation logic. To express rich specifications, the programmer can define inductive datatypes, primitive recursive pure functions over these datatypes, and abstract separation logic predicates. To verify these rich specifications, the programmer can write lemma functions, i.e., functions that serve only as proofs that their precondition implies their postcondition. The verifier checks that lemma functions terminate and do not have side-effects. Since neither VeriFast itself nor the underlying SMT solver need to do any significant search, verification time is predictable and low.

The VeriFast source code and binaries are released under the [MIT license](LICENSE.md).

Binaries
--------

A few minutes after each push to the master branch, binary packages become available at the following URLs:

- [Windows](https://ci.appveyor.com/api/projects/verifast/verifast/artifacts/src/verifast-nightly.zip?branch=master)
- [Linux/x64](http://82076e0e62875f063ae8-929808a701855dfb71539d0a4342d4be.r54.cf5.rackcdn.com/verifast-nightly.tar.gz)
- [OS X](http://82076e0e62875f063ae8-929808a701855dfb71539d0a4342d4be.r54.cf5.rackcdn.com/verifast-nightly-osx.tar.gz)

For the latest named releases, for now see [here](http://distrinet.cs.kuleuven.be/software/VeriFast/).

Simply extract the files from the archive to any location in your filesystem. All files in the archive are in a directory named `verifast-HASH` where `HASH` is the Git commit hash. For example, on Linux:

    tar xzf ~/Downloads/verifast-nightly.tar.gz
    cd verifast-<TAB>  # Press Tab to autocomplete
    bin/vfide examples/java/termination/Stack.jarsrc  # Launch the VeriFast IDE with the specified example
    ./test.sh  # Run the test suite (verifies all examples)

<<<<<<< HEAD

Automated VeriFast
==================
 
 By Mahmoud Mohsen\*, Bart Jacobs\*
 
 \* iMinds-DistriNet research group, Department of Computer Science, KU Leuven - University of Leuven, Belgium
 
 Automated VeriFast can be considered as an extension to VeriFast where some functionalities have been added to automatically generate predicates and infer function pre/post-conditions. In addition, it can automatically infer some of the inline annotations, such as some of the open commands. Automated VeriFast is an automation layer that exists on top of VeriFast. This automation layer doesn't not affect the verification process in any way, but on the other hand, it takes the output of the verification, in case of errors, and tries to infer some annotations that would solve this error. The interface of Automated VeriFast is the same as the normal VeriFast with two more buttons added. One button is for generating predicates and the other one for fixing the error. 
 
 Automated VeriFast source code and binaries are released under the [MIT license](LICENSE.md).
 
 For now, see [here](https://github.com/Mahmohsen/verifast/tree/Automated-Verifast) for source code and [here](https://github.com/Mahmohsen/verifast/tree/Automated-Verifast/Automated_Verifast_binary) for Windows binary releases.
=======
Compiling
---------
- [Windows](README.Windows.md)
- [Linux](README.Linux.md)
<<<<<<< HEAD
- [Mac OS X](README.MacOS.md)
>>>>>>> verifast/master
=======
- [OS X](README.MacOS.md)
>>>>>>> verifast/master

Documentation
-------------

- [The VeriFast Tutorial](https://people.cs.kuleuven.be/~bart.jacobs/verifast/tutorial.pdf)
- [Featherweight VeriFast](http://arxiv.org/pdf/1507.07697) [(Slides, handouts, Coq proof)](https://people.cs.kuleuven.be/~bart.jacobs/fvf)
- [Scientific papers](https://people.cs.kuleuven.be/~bart.jacobs/verifast/) on the various underlying ideas

Acknowledgements
----------------

This work is supported in part by the Flemish Research Fund (FWO-Vlaanderen), by the EU FP7 projects SecureChange, STANCE, and ADVENT, by Microsoft Research Cambridge as part of the Verified Software Initiative, and by the Research Fund KU Leuven.

Third-Party Resources
---------------------

- Kiwamu Okabe created a [Google Groups forum](https://groups.google.com/forum/#!forum/verifast) on VeriFast
- Kiwamu Okabe translated the VeriFast Tutorial into [Japanese](https://github.com/jverifast-ug/translate/blob/master/Manual/Tutorial/Tutorial.md). Thanks, Kiwamu!
