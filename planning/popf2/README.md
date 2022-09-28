# popf2
POPF2 planner from IPC 2011


```
@conference{colespopficaps,
  author = "A. J. Coles and A. I. Coles and M. Fox and D. Long",
  title = "Forward-Chaining Partial-Order Planning",
  booktitle = "Twentieth International Conference on Automated Planning and Scheduling (ICAPS 10)",
  year = "2010",
  publisher = "AAAI Press",
  month = "May"
}
```

```
@article{coles2011popf2,
  title={POPF2: A forward-chaining partial order planner},
  author={Coles, Amanda and Coles, Andrew and Fox, Maria and Long, Derek},
  journal={The 2011 International Planning Competition},
  pages={65},
  year={2011}
}
```


ORIGINAL README

About
-----

This directory contains the planner POPF2.  The original incarnation of POPF
is described in the ICAPS 2010 paper "Forward-Chaining Partial-Order Planning."
by Amanda Coles, Andrew Coles, Maria Fox and Derek Long.  This version
extends POPF by introducing any-time search, allowing it to optimise solution
quality.

Compiling
---------

POPF2 requires:
- cmake ( http://www.cmake.org/ )
- the CBC mixed integer programming solver ( https://projects.coin-or.org/Cbc/ )
- perl, bison and flex to build the parser

These are packaged with most linux distributions - on Ubuntu/Debian, the
following should suffice:

sudo apt-get install cmake coinor-libcbc-dev coinor-libclp-dev \
                     coinor-libcoinutils-dev bison flex

ALD: may also require coinor-libcgl-dev, coinor-libosi-dev


After that, run ./build


Running
-------

Run:

./plan <domain> <problem> <solution filename>

As POPF2 is an any-time planer, it will save sequentially numbered plans.
