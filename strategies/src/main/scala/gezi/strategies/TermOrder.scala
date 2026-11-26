package gezi.strategies

import gezi.ir.NativeSpecializer

/** A module of a normality degree: a function from a term to a value in a
  * well-founded total order, smaller better, computed as a fold one layer
  * at a time (`gezi/prolog/gezi/baseline/term_order.pl`, whose
  * module documentation this follows).
  *
  * The extraction builds a spelling one layer at a time over the entries of
  * the classes a production reads, and a module's FOLD STATE of a spelling
  * is a function of the production and its children's fold states only:
  * `folded` reads a layer whose children are leaves `OrderTerm.Folded`, each
  * the child's state at this module, and a whole term is a layer with no
  * such leaf. `rank` and `value` read the rank, whose order
  * (`OrderValue.ordering`) is the module's, smaller better, and the value, a
  * readable term, off a state. A module reads the structure of the term and
  * the definitions of the instructions in it (the shape of a definition, never a
  * name) and nothing else: no class, no history of the e-graph.
  */
trait NormalityModule[C <: NativeSpecializer & Singleton]:

  /** The module's name, by which a configuration names it. */
  def name: String

  /** The fold state of the layer (`module_folded/3`). */
  def folded(layer: OrderTerm[C], reading: TermReading[C]): FoldState

  /** The rank of the value of the term whose fold state is given
    * (`folded_rank/3`).
    */
  def rank(state: FoldState): OrderValue

  /** The value of the term whose fold state is given (`folded_value/3`). */
  def value(state: FoldState): OrderValue

  /** The READING of the state: what a parent's state reads of it beyond its
    * rank, finitely many readings for a graph
    * (`gezi.extraction.CostModel`, THE CONTRACT). Within one reading the
    * module's rank is monotone in its children's ranks, which
    * `CostMonotonicityLawTest` checks; the extraction keeps a class's best
    * entry of each reading. A module whose parent reads nothing beyond the
    * rank has one reading, the default.
    */
  def reading(state: FoldState): ModuleReading = ModuleReading.One

  /** Whether the module's cost meets the extraction's contract
    * (`gezi.extraction.CostModel`, THE CONTRACT): monotone within a
    * reading, and strictly monotone at priced positions. Every module states
    * it; an extraction refuses a module that does not
    * (`TermOrder.extractionModulesChecked`), and `CostMonotonicityLawTest`
    * checks the modules that say they do.
    */
  def meetsExtractionContract: Boolean

  /** The member of a choice the backend runs, given the members' readings at
    * this module, when the backend drops the others; nothing when it runs
    * them all, the default. A module that names one makes every module read
    * the others as unpriced (`ModuleCostModel.droppedChildren`), so that no
    * module prices what the backend drops.
    */
  def chosenChoiceMember(memberReadings: Vector[ModuleReading]): Option[Int] = None

  /** Whether the module may name children of an application or a parallel
    * that the backend compiles whatever their spelling (`compiledChildren`);
    * no by default, and then the extraction asks it nothing.
    */
  def compilesChildren: Boolean = false

  /** The positions of an application's or a parallel's children, its layer
    * given over its children's readings at this module (each child an
    * `OrderTerm.Unpriced`), whose spelling the backend compiles away, so that
    * what the run reads does not depend on it: every module reads them as
    * unpriced (`ModuleCostModel.droppedChildren`), as it reads a choice's
    * members the backend drops, and the extraction spells each by its
    * class's least entry of its reading. None by default.
    */
  def compiledChildren(layer: OrderTerm[C], reading: TermReading[C]): Vector[Boolean] = layer match
    case OrderTerm.Apply(_, _) | OrderTerm.Parallel(_, _, _) => Vector(false, false)
    case _                                                   => Vector.empty

  /** The module's fold of codes layer by layer (`CodeFolding`), when it
    * has one; none by default, and then the extraction reads a thunk's inner
    * thunks whole, listing every combination of the readings of the fillings
    * under them (`ThunkCandidates`), exact and exponential in their number.
    * The extraction folds a thunk's code by parts only when every module of
    * its model has one.
    */
  def codeFolding: Option[CodeFolding[C]] = None

/** A module that is one object for every configuration: its operations are generic in the configuration, and `at` gives
  * it as the module of one (`NormalityModule`). A module that holds a configuration of its own implements
  * `NormalityModule` directly.
  */
trait ConfigurationFreeModule:

  /** The module's name, by which a configuration names it. */
  def name: String

  /** The fold state of the layer (`module_folded/3`). */
  def folded[C <: NativeSpecializer & Singleton](layer: OrderTerm[C], reading: TermReading[C]): FoldState

  /** The rank of the value of the term whose fold state is given
    * (`folded_rank/3`).
    */
  def rank(state: FoldState): OrderValue

  /** The value of the term whose fold state is given (`folded_value/3`). */
  def value(state: FoldState): OrderValue

  /** The READING of the state: what a parent's state reads of it beyond its
    * rank, finitely many readings for a graph
    * (`gezi.extraction.CostModel`, THE CONTRACT). Within one reading the
    * module's rank is monotone in its children's ranks, which
    * `CostMonotonicityLawTest` checks; the extraction keeps a class's best
    * entry of each reading. A module whose parent reads nothing beyond the
    * rank has one reading, the default.
    */
  def reading(state: FoldState): ModuleReading = ModuleReading.One

  /** Whether the module's cost meets the extraction's contract
    * (`gezi.extraction.CostModel`, THE CONTRACT): monotone within a
    * reading, and strictly monotone at priced positions. Every module states
    * it; an extraction refuses a module that does not
    * (`TermOrder.extractionModulesChecked`), and `CostMonotonicityLawTest`
    * checks the modules that say they do.
    */
  def meetsExtractionContract: Boolean

  /** The member of a choice the backend runs, given the members' readings at
    * this module, when the backend drops the others; nothing when it runs
    * them all, the default. A module that names one makes every module read
    * the others as unpriced (`ModuleCostModel.droppedChildren`), so that no
    * module prices what the backend drops.
    */
  def chosenChoiceMember(memberReadings: Vector[ModuleReading]): Option[Int] = None

  /** Whether the module may name children of an application or a parallel
    * that the backend compiles whatever their spelling (`compiledChildren`);
    * no by default, and then the extraction asks it nothing.
    */
  def compilesChildren: Boolean = false

  /** The positions of an application's or a parallel's children, its layer
    * given over its children's readings at this module (each child an
    * `OrderTerm.Unpriced`), whose spelling the backend compiles away, so that
    * what the run reads does not depend on it: every module reads them as
    * unpriced (`ModuleCostModel.droppedChildren`), as it reads a choice's
    * members the backend drops, and the extraction spells each by its
    * class's least entry of its reading. None by default.
    */
  def compiledChildren[C <: NativeSpecializer & Singleton](layer: OrderTerm[C], reading: TermReading[C]): Vector[Boolean] = layer match
    case OrderTerm.Apply(_, _) | OrderTerm.Parallel(_, _, _) => Vector(false, false)
    case _                                                   => Vector.empty

  /** The module's fold of codes layer by layer (`CodeFolding`), when it
    * has one; none by default, and then the extraction reads a thunk's inner
    * thunks whole, listing every combination of the readings of the fillings
    * under them (`ThunkCandidates`), exact and exponential in their number.
    * The extraction folds a thunk's code by parts only when every module of
    * its model has one.
    */
  def codeFolding[C <: NativeSpecializer & Singleton]: Option[CodeFolding[C]] = None

  /** The module as a module of the configuration `C`: each operation the one this object gives. */
  final def at[C <: NativeSpecializer & Singleton]: NormalityModule[C] = new NormalityModule[C]:
    def name: String = ConfigurationFreeModule.this.name
    def folded(layer: OrderTerm[C], reading: TermReading[C]): FoldState = ConfigurationFreeModule.this.folded(layer, reading)
    def rank(state: FoldState): OrderValue = ConfigurationFreeModule.this.rank(state)
    def value(state: FoldState): OrderValue = ConfigurationFreeModule.this.value(state)
    override def reading(state: FoldState): ModuleReading = ConfigurationFreeModule.this.reading(state)
    def meetsExtractionContract: Boolean = ConfigurationFreeModule.this.meetsExtractionContract
    override def chosenChoiceMember(memberReadings: Vector[ModuleReading]): Option[Int] =
      ConfigurationFreeModule.this.chosenChoiceMember(memberReadings)
    override def compilesChildren: Boolean = ConfigurationFreeModule.this.compilesChildren
    override def compiledChildren(layer: OrderTerm[C], reading: TermReading[C]): Vector[Boolean] =
      ConfigurationFreeModule.this.compiledChildren(layer, reading)
    override def codeFolding: Option[CodeFolding[C]] = ConfigurationFreeModule.this.codeFolding[C]

/** A reading of a fold state (`NormalityModule.reading`): readings are
  * compared by equality only.
  */
trait ModuleReading

object ModuleReading:

  /** The reading of a module whose parents read nothing beyond its rank. */
  case object One extends ModuleReading

/** The configuration of a normality degree: its modules from the highest
  * priority to the lowest. The normality degree of a term is the list of its
  * ranks in that order, compared lexicographically. It names no module: the
  * caller gives the table of the modules it runs with.
  */
object TermOrder:

  /** The modules of the table named, in the order named. Throws
    * `TermOrderError` with `NotAModule` for a name the table has not and
    * with `ModuleTwice` for a name given twice (`modules_checked/1`).
    */
  def modulesChecked[C <: NativeSpecializer & Singleton](table: Vector[NormalityModule[C]], names: Vector[String]): Vector[NormalityModule[C]] =
    val modules = names.map(name =>
      table
        .find(_.name == name)
        .getOrElse(throw TermOrderError(TermOrderErrorReason.NotAModule(name)))
    )
    names.sorted.zip(names.sorted.drop(1)).find(_ == _).foreach { (twice, _) =>
      throw TermOrderError(TermOrderErrorReason.ModuleTwice(twice))
    }
    modules

  /** The modules, refused for an extraction when one does not meet the
    * extraction's contract (`NormalityModule.meetsExtractionContract`):
    * throws `TermOrderError` with `NotForExtraction` naming it, since the
    * extraction's kept entries are the least trees only under the contract
    * (no silent use of (A)'s exactness claim with a module that breaks it).
    */
  def extractionModulesChecked[C <: NativeSpecializer & Singleton](modules: Vector[NormalityModule[C]]): Vector[NormalityModule[C]] =
    modules.find(!_.meetsExtractionContract).foreach(module =>
      throw TermOrderError(TermOrderErrorReason.NotForExtraction(module.name))
    )
    modules

  /** The state as a module expects it, the state of its own kind; throws
    * `TermOrderError` with `NotATerm` for a state of another module.
    */
  def ownState[State <: FoldState](state: FoldState)(using tag: scala.reflect.ClassTag[State]): State =
    state match
      case own: State => own
      case other      => throw TermOrderError(TermOrderErrorReason.NotATerm(OrderTerm.Folded[Nothing](other, false)))

  /** The term no module folds, refused: a child of a stored layer. */
  def refused[C <: NativeSpecializer & Singleton](term: OrderTerm[C]): Nothing =
    throw TermOrderError(TermOrderErrorReason.NotATerm(term))
