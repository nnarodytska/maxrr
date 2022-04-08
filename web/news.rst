====
News
====

PySAT is being developed with the *rolling release* model, which means we do
not deliver major releases from time to time. Instead, many small (sometimes
tiny) and frequent updates are provided. As a result, `upgrading
<installation.html>`_ your installation of the toolkit every now to keep it up
to date and then is good idea.

Changelog and more
------------------

22.02.2022 (*0.1.7.dev16*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Fixed a minor issue in RC2 related to making useless iterations in core
  minimization.
- Added support for WCNF+ formulas in OptUx.

04.12.2021 (*0.1.7.dev15*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Fixed a minor bug in stratified RC2 related to model enumeration for empty
  formulas.
- Updated Hitman so that it opts for plain RC2 if all weights are the same.
- Fixed cost MUS computation in OptUx.

24.11.2021 (*0.1.7.dev14*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Another attempt to fix the bug in topw handling if unspecified.

24.11.2021 (*0.1.7.dev13*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Fixed a minor issue in fm.py related to handling native AM1 constraints.
- Fixed a bug in WCNF parser, which caused incorrect top weight computation if
  not specified in the preamble of the file explicitly.

09.11.2021 (*0.1.7.dev12*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Fixed a bug related to handling CNF formulas and improper updating IDPool
  for PB constraints in the case of no auxiliary variables.

12.10.2021 (*0.1.7.dev11*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Fixed a bug related to meaningless bounds in cardinality constraints (both
  AtMost and AtLeast).

17.08.2021 (*0.1.7.dev10*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Added cluster-based stratification to :class:`RC2`.
- Made the selection of stratification strategy in :class:`RC2` optional.

02.08.2021 (*0.1.7.dev9*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Added proper handling of border cases when creating cardinality constraints.
  Done for all encodings, and both AtMostK and AtLeastK constraints.
- Added an ``UnsupportedBound`` exception to be raised whenever *pairwise*,
  *bitwise*, or *ladder* encodings are created with the bound in :math:`(1, N
  - 1)`.

30.07.2021 (*0.1.7.dev8*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Fixed a bug in :class:`IDPool` introduced in ``0.1.7.dev7``, related to
  ``None`` handling.

28.07.2021 (*0.1.7.dev7*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Updated :class:`IDPool` to return a new variable ID without an object.
- Updated :class:`RC2` to support IDPool instead of `self.topv`.

17.07.2021 (*0.1.7.dev6*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Modified the implemention of the am1 heuristic in :class:`RC2`.

26.06.2021 (*0.1.7.dev5*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Got rid of relaxation variables in :class:`RC2` - minor issue, which might
  still have affected the performance.

11.06.2021 (*0.1.7.dev4*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Fixed compilation issues occurring for cadical on macOS >= 11.3 with the
  most recent version of clang. Thanks to András Salamon.

24.05.2021 (*0.1.7.dev3*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Added a warning in `enum_models()` regarding unsatisfiability of the formula
  after model enumeration is finished.
- Fixed a couple of bugs in :class:`FM`.
- Similar changes in other example implementations.

20.04.2021 (*0.1.7.dev2*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Improved the sequential counters encoding based on Donald Knuth's
  irredundant variant, following the suggestion of Alex Healy.

31.03.2021 (*0.1.7.dev1*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- An attempt to fix compilation issues of Mergesat.

31.03.2021 (*0.1.7.dev0*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Added basic interface to :class:`Mergesat3`.
- Ported :class:`Minicard`'s native cardinality support to Glucose, which
  resulted in solvers :class:`Gluecard3` and :class:`Gluecard4`.
- Added translation of :class:`Cadical`'s binary DRUP format to text-based.

25.03.2021 (*0.1.6.dev16*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- A few minor corrections in :class:`RC2`, :class:`RC2Stratified`, and
  :class:`Hitman` addressing the issues related to empty formulas.

23.03.2021 (*0.1.6.dev15*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- A minor correction in :class:`OptUx` related to MUS cost value.

23.03.2021 (*0.1.6.dev14*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- A minor correction in the ``setup.py`` script.

23.03.2021 (*0.1.6.dev13*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Added a way to bootstrap :class:`.LBX` and :class:`.MCSls` for computing
  MCSes that include a specified subset of clauses.
- Updated :class:`Hitman` to support *weighted* hitting set problems.
- Added :class:`.OptUx`, which is an smallest/optimal MUS extractor and
  enumerator that aims to replicate the performance of Forqes.

13.02.2021 (*0.1.6.dev12*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Fixed formula dumping in other formats (see :meth:`to_alien`).

24.11.2020 (*0.1.6.dev11*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Added formula dumping in SMT-LIB2 (see :meth:`to_alien`).

19.11.2020 (*0.1.6.dev10*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Fixed the number of propagations ins MapleChrono.

27.09.2020 (*0.1.6.dev9*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Fixed a bug in copying of :class:`CNFPlus` and :class:`WCNFPlus` objects.
- Added an attempt to write down OPB and LP formats (likely to be buggy!).

26.09.2020 (*0.1.6.dev8*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Fixed a bug in `solvers.py` related to the :class:`CNFPlus` iterator.

25.09.2020 (*0.1.6.dev7*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Added an example for accum_stats().
- Fixed a minor bug in musx example.
- A few fixes in :mod:`pysat.formula`.
- Fixed an issue in :mod:`pysat.card` related to non-list literals.

09.08.2020 (*0.1.6.dev6*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Using int64_t for accum_stats().

03.08.2020 (*0.1.6.dev5*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Fixed the bug of wrong top_id when no cardinality encoding is created.

26.07.2020 (*0.1.6.dev4*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Accumulated stats for other solvers.
- More enumeration-related fixes in RC2Stratified.

07.07.2020 (*0.1.6.dev3*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Fixed RC2's enumeration of MSSes.
- Minor changes to the patch for CaDiCaL

06.07.2020 (*0.1.6.dev2*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Forgot to manifest the solver archives. :)

06.07.2020 (*0.1.6.dev1*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Solver archive files are now shipped with PySAT.
- A bit cleaner signal handling.
- Got rid of the segmentation faults when CTRL+C'ing limited SAT calls.
- Accumulated stats for Glucose4.1 (by Chris Jefferson)

04.07.2020 (*0.1.5.dev17*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Removed dependency for zlib.

23.06.2020 (*0.1.5.dev16*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Fixed a minor bug in top id handling in :mod:`pysat.card` reported by Pedro
  Bonilla.

15.06.2020 (*0.1.5.dev15*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- A few more minor changes in RC2 to fulfill the requirements of MSE 2020.

18.05.2020 (*0.1.5.dev14*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- A few minor changes in RC2 addressing a new v-line format and the top-k
  track.

05.05.2020 (*0.1.5.dev13*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- A few minor issues related to non-deterministic behavior of sets in Python3.

12.04.2020 (*0.1.5.dev12*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Fixed a minor bug in garbage collector of RC2.
- Fixed an empty-core bug in RC2 appearing in solution enumeration.

19.03.2020 (*0.1.5.dev10*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Floating point arithmetic is now done through the :mod:`decimal` module to
  avoid precision issues.

19.03.2020 (*0.1.5.dev9*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Minor issue fixed in :class:`RC2Stratified`.

17.03.2020 (*0.1.5.dev8*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Added support of floating point weights in :class:`WCNF` and
  :class:`WCNFPlus`.
- Added support of negative weights.

14.03.2020 (*0.1.5.dev7*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Another minor fix in :mod:`pysat.formula` related to importing py-aiger-cnf.

24.01.2020 (*0.1.5.dev6*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Fixed a minor bug related to unknown keyword arguments passed to the
  constructor of :class:`Solver`.

08.01.2020 (*0.1.5.dev5*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Added support of copying :class:`CNFPlus` and :class:`WCNFPlus` formulas.

04.12.2019 (*0.1.5.dev2*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Fixed yet another issue related to :class:`pysat.formula.CNFPlus` and
  :class:`pysat.solvers.Minicard`.
- Replaced :meth:`time.clock()` with :meth:`time.process_time()` for Python
  3.8 and newer.

04.12.2019 (*0.1.5.dev1*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Added Windows support (**many** thanks to `Rüdiger Jungbeck
  <https://github.com/rjungbeck>`__!).
- Fixed a few more issues related to :class:`pysat.formula.CNFPlus` and
  :class:`pysat.formula.WCNFPlus`.

02.12.2019 (*0.1.4.dev25*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Fixed the parser of :class:`pysat.formula.WCNFPlus` formulas.
- Fixed a bug in method :meth:`append_formula` for
  :class:`pysat.solvers.Minicard`.

28.11.2019 (*0.1.4.dev24*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Fixed signal handling in the multithreaded use of PySAT. Multiple oracles
  can be used at a time now.

14.11.2019 (*0.1.4.dev23*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Fixed a minor bug in :mod:`pysat.examples.lsu`.

07.11.2019 (*0.1.4.dev22*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- A minor fix in :mod:`pysat.formula` related to importing py-aiger-cnf.

30.10.2019 (*0.1.4.dev21*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Marked py-aiger-cnf as an optional dependency.

29.10.2019 (*0.1.4.dev20*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- The use of py-aiger is replaced by py-aiger-cnf to incapsulate the internals
  of py-aiger.

09.10.2019 (*0.1.4.dev19*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Added solution optimality check in :mod:`pysat.examples.lsu`.
- Added a way to update the used variable identifiers using
  :class:`pysat.formula.IDPool` when working with
  :class:`pysat.card.CardEnc.*` and :class:`pysat.pb.PBEnc.*`.
- Minor cosmetic changes.
- New logo.

30.09.2019 (*0.1.4.dev18*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Fixed a bug related to using py-aiger on Python 2.

28.08.2019 (*0.1.4.dev17*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Updated the minimum version of py-aiger required for installation.

28.08.2019 (*0.1.4.dev16*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- CNF formulas can now be bootstrapped by Tseitin-encoding AIGER circuits.
  This is done with the use of the `py-aiger package
  <https://github.com/mvcisback/py-aiger>`__.

21.08.2019 (*0.1.4.dev15*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Added rudimentary support of CaDiCaL.

04.06.2019 (*0.1.4.dev13*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Fixed the wrong number of variables after calling methods of :class:`CardEnc`.
- Added clause iterator to :class:`CNF`.
- Calling :class:`CardEnc.*([])` returns an empty CNF formula.

25.06.2019 (*0.1.4.dev12*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Corrected a typo in the method name :meth:`WCNF.unweighted`.

17.06.2019 (*0.1.4.dev11*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Added top weight update when adding soft clauses into a WCNF.

26.05.2019 (*0.1.4.dev10*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Added support for non-deterministic interruption, e.g. based on a timer.

17.05.2019 (*0.1.4.dev9*)
~~~~~~~~~~~~~~~~~~~~~~~~~

- Minor fixes related to the WCNF+ support in :mod:`pysat.examples.lsu`,
  :mod:`pysat.examples.lbx`, and :mod:`pysat.examples.mcsls`.

27.04.2019 (*0.1.4.dev8*)
~~~~~~~~~~~~~~~~~~~~~~~~~

- Made an attempt to fix the C++ library issue on MacOS.

19.04.2019 (*0.1.4.dev7*)
~~~~~~~~~~~~~~~~~~~~~~~~~

- Fixed a couple of minor issues in :mod:`pysat.examples.hitman` and
  :mod:`pysat.example.mcsls`.

21.03.2019 (*0.1.4.dev6*)
~~~~~~~~~~~~~~~~~~~~~~~~~

- Fixed a potential bug related to "deallocating None".

19.03.2019 (*0.1.4.dev5*)
~~~~~~~~~~~~~~~~~~~~~~~~~

- Fixed an issue in :func:`.propagate` for the MapleChrono solver.

18.03.2019 (*0.1.4.dev3*)
~~~~~~~~~~~~~~~~~~~~~~~~~

- Some fixes in the assumption handling of the Maple* solvers.

17.03.2019 (*0.1.4.dev2*)
~~~~~~~~~~~~~~~~~~~~~~~~~

- Added three solvers of the Maple family: Maplesat (i.e. MapleCOMSPS_LRB),
  MapleCM, and MapleChrono (i.e. MapleLCMDistChronoBT).
- A few minor fixes.

13.03.2019 (*0.1.4.dev1*)
~~~~~~~~~~~~~~~~~~~~~~~~~

- Added :mod:`pysat.pb` providing access to a few PB constraints with the use
  of PyPBLib.
- A number of small fixes.

28.12.2018 (*0.1.3.dev25*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Fixed model enumerator in :mod:`pysat.examples.rc2`.
- Documented :mod:`pysat.examples.rc2`.

01.11.2018 (*0.1.3.dev24*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Documented a few example modules including :mod:`pysat.examples.lbx`,
  :mod:`pysat.examples.mcsls`, and :mod:`pysat.examples.lsu`.

22.09.2018 (*0.1.3.dev23*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Added the image of the FLOC medals to the webpage.
- Added the news section to the webpage.
- Removed unused source code.

20.09.2018 (*0.1.3.dev22*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Added better support for iterables in :mod:`pysat.card` and
  :mod:`pysat.solvers`.
- Added documentation for ``examples/fm.py``, ``examples/genhard.py``,
  ``examples/hitman.py`` and ``examples/musx.py``.

06.09.2018 (*0.1.3.dev21*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Fixed a typo in the project description on `PyPI
  <https://pypi.org/project/python-sat/>`_.

30.08.2018 (*0.1.3.dev20*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Added an implementation of the LSU algorithm for MaxSAT.
- Fixed a bug in :mod:`pysat._fileio` appearing when LZMA is not present.

25.08.2018 (*0.1.3.dev19*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Solvers can receive ``iterables`` as clauses (besides ``lists``).
- Fixed a minor issue in ``examples/hitman.py``.

25.08.2018 (*0.1.3.dev18*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Cosmetic changes in the documentation.

25.08.2018 (*0.1.3.dev17*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- More incremental functionality in RC2, LBX, and MCSls.
- Added a minimal hitting set enumerator as another example.

20.08.2018 (*0.1.3.dev16*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Fixed a problem appearing when no model exists.

19.08.2018 (*0.1.3.dev15*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Added support for reading and writing with \*zipped files.
- Added the corresponding capabilities to the examples.

17.08.2018 (*0.1.3.dev14*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Fixed a couple of minor issues related to Python 3 (in RC2 and iterative
  totalizer).

27.07.2018 (*0.1.3.dev13*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Added support for setting variable *phases* (*user-preferred polarities*).

16.07.2018 (*0.1.3.dev12*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Added incremetal model enumeration to RC2.
- Fixed a couple of minor issues in LBX and MCSls.
- Added mutilated chessboard princimple formulas for ``examples/genhard.py``.

12.07.2018 (RC2)
~~~~~~~~~~~~~~~~

MaxSAT solver RC2 won both *unweighted* and *weighted* categories of the main
track of `MaxSAT Evaluation 2018
<https://maxsat-evaluations.github.io/2018/rankings.html>`_ and got two medals
at `FLOC 2018 Olympic Games <https://www.floc2018.org/floc-olympic-games/>`_!

.. image:: medals.svg
   :width: 270 px
   :align: left

20.06.2018 (*0.1.3.dev11*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Added the webpage for the toolkit.
- The first draft of the documentation.

07.06.2018 (*0.1.3.dev10*)
~~~~~~~~~~~~~~~~~~~~~~~~~~

- Fixed a minor bug in iterative totalizer.
- Added modes A and B to RC2 for MaxSAT evaluation 2018.

28.05.2018 (*0.1.3.dev9*)
~~~~~~~~~~~~~~~~~~~~~~~~~

- Added a way to manually set off a previously set budget on the number of
  clauses or propagations.
- Added an optional core minimization in RC2.

25.05.2018 (*0.1.3.dev8*)
~~~~~~~~~~~~~~~~~~~~~~~~~

- Fixed *long_description* of the project. Corrected the GitHub reference.
- Implemented hidden AtMost1 constraint detection in RC2.
- Improved support for Python 3 in RC2.
- A few more minor issues in RC2 got fixed.

23.05.2018 (*0.1.3.dev7*)
~~~~~~~~~~~~~~~~~~~~~~~~~

- Added optional *phase saving* in literal propagation.
- Fixed a bug in literal propagation.

22.05.2018 (*0.1.3.dev6*)
~~~~~~~~~~~~~~~~~~~~~~~~~

- More fixes in literal propagation and its interface.

21.05.2018 (*0.1.3.dev5*)
~~~~~~~~~~~~~~~~~~~~~~~~~

- A minor modification of literal propagation.

21.05.2018 (*0.1.3.dev4*)
~~~~~~~~~~~~~~~~~~~~~~~~~

- Added *literal propagation* in MiniSat-like solvers, i.e. ``Minisat22``,
  ``MinisatGH``, ``Minicard``, ``Glucose3``, and ``Glucose41``.

15.05.2018 (*0.1.3.dev3*)
~~~~~~~~~~~~~~~~~~~~~~~~~

- Another attempt to fix installation. Mirrored GitHub-hosted solvers.

02.05.2018 (*0.1.3.dev2*)
~~~~~~~~~~~~~~~~~~~~~~~~~

- Modified signal handling in ``pysolvers`` and ``pycard``.
- Fixed a couple of minor issues in iterative totalizer.
- Reimplemented ``examples/genhard.py``. Each family of formulas is not a
  class.

10.04.2018 (*0.1.3.dev1*)
~~~~~~~~~~~~~~~~~~~~~~~~~

- Fixed a bug in *limited* SAT solving, i.e. in solving within a given
  *budget* on the number of conflicts or the number of propagations.

09.04.2018 (*0.1.3.dev0*)
~~~~~~~~~~~~~~~~~~~~~~~~~

- Improved ``README.rst``.
- Minor modifications in ``examples/genhard.py``.
- Added example scripts installation as executables.

08.04.2018 (*0.1.2.dev9*)
~~~~~~~~~~~~~~~~~~~~~~~~~

- Fixed a couple of minor bugs in :mod:`pysat.card` and :mod:`pysat.formula`.

06.04.2018 (*0.1.2.dev8*)
~~~~~~~~~~~~~~~~~~~~~~~~~

- Added a couple of optimizations to ``examples/rc2.py`` including
  *unsatisfiable core trimming* and *core exhaustion*.
- Added :class:`SolverNames` to simplify a solver selection.
- An attempt to make the installation process less fragile.

03.04.2018 (*0.1.2.dev7*)
~~~~~~~~~~~~~~~~~~~~~~~~~

- Fixed incremental mode of Glucose 4.1.
- Added support for Minicard's native cardinality constraints in
  ``examples/fm.py``.
- Added RC2 as an example of a MaxSAT solver.
- Fixed a minor issue in iterative totalizer.

29.03.2018 (*0.1.2.dev6*)
~~~~~~~~~~~~~~~~~~~~~~~~~

- Fixed a bug in iterative totalizer, which led to clause duplication.

28.03.2018 (*0.1.2.dev5*)
~~~~~~~~~~~~~~~~~~~~~~~~~

- Added iterative totalizer to :mod:`pysat.card`.
- Added solver download caching (i.e. a solver is not downloaded more than once).

25.03.2018 (*0.1.2.dev4*)
~~~~~~~~~~~~~~~~~~~~~~~~~

- Added support for Glucose 4.1.

06.03.2018 (*0.1.2.dev3*)
~~~~~~~~~~~~~~~~~~~~~~~~~

- Added ``examples/genhard.py`` illustrating the work with the
  :mod:`pysat.formula` module.
- Added :class:`pysat.formula.IDPool`, a simple manager of *variable
  identifiers*.

04.03.2018 (*0.1.2.dev2*)
~~~~~~~~~~~~~~~~~~~~~~~~~

- Fixed a bug related to SAT oracle's timer.

02.03.2018 (*0.1.2.dev1*)
~~~~~~~~~~~~~~~~~~~~~~~~~

- Fixed a number of issues in ``examples/fm.py``, ``examples/lbx.py``, and
  ``examples/musx.py`` for a better support of Python 3.

01.03.2018 (*0.1.1.dev9*)
~~~~~~~~~~~~~~~~~~~~~~~~~

- Minor fixes in ``README.rst``.

22.02.2018 (*0.1.1.dev8*)
~~~~~~~~~~~~~~~~~~~~~~~~~

- Minor changes in :mod:`pysat.card`.
- A few typos in :mod:`pysat.examples.fm`.
- Fixed *author_email* in ``setup.py``.

11.02.2018 (*0.1.1.dev7*)
~~~~~~~~~~~~~~~~~~~~~~~~~

- Initial commit accompanying the `corresponding SAT submission
  <citation.html>`_.
