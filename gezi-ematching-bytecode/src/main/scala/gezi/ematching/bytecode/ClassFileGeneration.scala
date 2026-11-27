package gezi.ematching.bytecode

// DOWNGRADE of CONTRIBUTING.md's immutability rule ("The code is 100% immutable"), local to one call. The user,
// 2026-10-31: "这里可以作为例外，在局部使用可变的 builder" (about
// java.lang.classfile's mutable builders). The builders below are used only
// inside the call `ClassFileGeneration.generated`, which turns one program
// into a defined class: no builder, label or byte array is stored, returned
// or shared; the call returns the class's one instance, through the
// immutable interface `GeneratedProgram`.

import java.lang.classfile.ClassBuilder
import java.lang.classfile.ClassFile
import java.lang.classfile.ClassHierarchyResolver
import java.lang.classfile.CodeBuilder
import java.lang.classfile.Label
import java.lang.classfile.TypeKind
import java.lang.classfile.instruction.SwitchCase
import java.lang.constant.ClassDesc
import java.lang.constant.ConstantDescs
import java.lang.constant.DynamicConstantDesc
import java.lang.constant.MethodTypeDesc
import java.lang.invoke.MethodHandles
import gezi.egraph.GraphBuilding
import gezi.egraph.GraphView
import gezi.egraph.Head
import gezi.egraph.MemberShape
import gezi.egraph.PositionRole
import gezi.egraph.PositionUser
import gezi.egraph.UserRole
import gezi.ematching.Building
import gezi.ematching.LayerTemplate
import gezi.ematching.Matching
import gezi.ematching.Program
import gezi.ematching.SeedTree
import gezi.ematching.Step
import gezi.ir.Code
import gezi.ir.NativeSpecializer
import gezi.ir.Layer
import scala.jdk.CollectionConverters.*
import gezi.ir

/** The class file of a program, generated and defined as a hidden class.
  *
  * The class has a public constructor, the four methods of `GeneratedProgram`,
  * each a switch on its number, and static methods: one per entry, the tree of
  * a kind and key's seeds (`entry<n>(GraphView, int) -> Matching`), one per
  * added side (`added<n>`), shared subterm (`shared<n>`) and code body
  * (`body<n>`, n the number this compilation gave the code), each
  * `(GraphBuilding, Vector) -> Tuple2`. Its constants, instructions and codes
  * among them, are its class data, a list read by `MethodHandles.classDataAt`.
  */
private object ClassFileGeneration:

  private def described(runtimeClass: Class[?]): ClassDesc =
    ClassDesc.ofDescriptor(runtimeClass.descriptorString)

  private val generatedClass =
    ClassDesc.of("gezi.ematching.bytecode.GeneratedProgramClass")
  private val generatedInterface = described(classOf[GeneratedProgram])
  private val support =
    ClassDesc.of("gezi.ematching.bytecode.GeneratedCodeSupport")
  private val graphView = described(classOf[GraphView[?]])
  private val graphBuilding = described(classOf[GraphBuilding[?, ?]])
  private val matchingClass = described(classOf[Matching])
  private val searchedClass = described(classOf[Searched])
  // A layer is a union of constructor classes and an instruction or a code an
  // opaque alias of AnyRef: none is a class, so each descriptor is the
  // erasure the Scala compiler gave a method whose signature names the type.
  private val layerClass = described(
    classOf[GraphView[?]].getMethod("layer", Integer.TYPE).getReturnType
  )
  private val instructionClass = described(
    classOf[GraphView[?]]
      .getMethod("instructionNode", classOf[AnyRef])
      .getParameterTypes
      .head
  )
  // A code is the same opaque alias of AnyRef as an instruction, so it erases alike.
  private val codeIdentifierClass = instructionClass
  private val applyLayer = described(classOf[ir.Apply[?]])
  private val parallelLayer = described(classOf[ir.Parallel[?]])
  private val choiceLayer = described(classOf[ir.Choice[?]])
  private val thunkLayer = described(classOf[ir.Thunk[?]])
  private val vectorClass = described(classOf[Vector[?]])
  private val optionClass = described(classOf[Option[?]])
  private val someClass = described(classOf[Some[?]])
  private val tupleClass = described(classOf[(?, ?)])
  private val positionUserClass = described(classOf[PositionUser])
  private val headClass = described(classOf[Head[?]])
  private val memberShapeClass = described(classOf[MemberShape])
  private val userRoleClass = described(classOf[UserRole])
  private val positionRoleClass = described(classOf[PositionRole])
  private val boxes = ClassDesc.of("scala.runtime.BoxesRunTime")
  private val objectClass = ConstantDescs.CD_Object
  private val integer = ConstantDescs.CD_int
  private val boolean = ConstantDescs.CD_boolean

  private def method(
      result: ClassDesc,
      parameters: ClassDesc*
  ): MethodTypeDesc =
    MethodTypeDesc.of(result, parameters*)

  private val entryType = method(matchingClass, graphView, integer)
  private val buildingType = method(tupleClass, graphBuilding, vectorClass)

  /** The constant a step or a building names, with the class it is read as. */
  private def constantOf(value: AnyRef): ClassDesc = value match
    case _: Head[?]      => headClass
    case _: MemberShape  => memberShapeClass
    case _: UserRole     => userRoleClass
    case _: PositionRole => positionRoleClass
    case _: Vector[?]    => vectorClass
    case _: Searched     => searchedClass
    // An instruction or a code: an interned constructor object.
    case _: (ir.Apply[?] | ir.Parallel[?] | ir.Choice[?] | ir.Thunk[?] |
          ir.UriNode | ir.Opaque | ir.Slot) =>
      instructionClass
    case other =>
      throw IllegalArgumentException(
        s"no constant of the class ${other.getClass}"
      )

  private def stepConstants[C <: NativeSpecializer & Singleton](
      step: Step[C]
  ): Vector[AnyRef] = step match
    case Step.Layer(_, LayerTemplate.Thunk(code, holes), _) =>
      Vector(code, holes)
    case Step.Lookup(LayerTemplate.Thunk(code, holes), _, _) =>
      Vector(code, holes)
    case Step.InstructionIn(instruction, _) =>
      Vector(instruction.representation)
    case Step.InstructionNode(instruction, _) =>
      Vector(instruction.representation)
    case Step.EachHeadMember(_, head, _)      => Vector(head)
    case Step.EachMember(_, shape, _)         => Vector(shape)
    case Step.EachUser(_, role, _)            => Vector(role)
    case Step.EachPositionUser(_, role, _, _) => Vector(role)
    case Step.Once(steps)                     => steps.flatMap(stepConstants)
    case _                                    => Vector.empty

  private def buildingConstants[C <: NativeSpecializer & Singleton](
      building: Building[C]
  ): Vector[AnyRef] = building match
    case Building.Apply(function, argument, _) =>
      buildingConstants(function) ++ buildingConstants(argument)
    case Building.Parallel(left, right) =>
      buildingConstants(left) ++ buildingConstants(right)
    case Building.Choice(left, right) =>
      buildingConstants(left) ++ buildingConstants(right)
    case Building.Thunk(code, holes, fillings) =>
      Vector(code, holes) ++ fillings.flatMap(buildingConstants)
    case Building.InstructionNode(instruction) =>
      Vector(instruction.representation)
    case Building.CodeBody(body) => Vector(body)
    case Building.Value(_)       => Vector.empty

  /** The registers a step reads or writes, those of a witness's steps included.
    */
  private def registersOf[C <: NativeSpecializer & Singleton](
      step: Step[C]
  ): Vector[Int] = step match
    case Step.Layer(node, _, children)             => node +: children
    case Step.Root(node, target)                   => Vector(node, target)
    case Step.Same(first, second)                  => Vector(first, second)
    case Step.InstructionIn(_, root)               => Vector(root)
    case Step.HasClosure(root)                     => Vector(root)
    case Step.EachHeadMember(root, _, target)      => Vector(root, target)
    case Step.EachMember(root, _, target)          => Vector(root, target)
    case Step.EachUser(root, _, target)            => Vector(root, target)
    case Step.EachPositionUser(root, _, _, target) => Vector(root, target)
    case Step.InstructionNode(_, target)           => Vector(target)
    case Step.Lookup(_, children, target)          => children :+ target
    case Step.Once(steps)                          => steps.flatMap(registersOf)

  /** The steps of the tree, its branches' included. */
  private def treeSteps[C <: NativeSpecializer & Singleton](
      tree: SeedTree[C]
  ): Vector[Step[C]] =
    tree.steps ++ tree.branches.flatMap(treeSteps)

  /** The program's class defined, and its one instance. The entries are the
    * trees of the kinds and keys, each with its number of seeds, in the order
    * the backend numbered them; each code of the program has the number the
    * backend gave it.
    */
  def generated[C <: NativeSpecializer & Singleton](
      program: Program[C],
      entries: Vector[(SeedTree[C], Int)],
      codeNumbers: Map[Code, Int]
  ): GeneratedProgram =
    val shared = program.orientations.flatMap(_.shared)
    val codes = program.codes.toVector.sortBy((code, _) => codeNumbers(code))
    val constants =
      (entries.flatMap((tree, _) => treeSteps(tree).flatMap(stepConstants)) ++
        entries.map((_, seedCount) =>
          GeneratedCodeSupport.searchStarted(seedCount)
        ) ++
        program.orientations.flatMap(plan => buildingConstants(plan.added)) ++
        shared.flatMap(buildingConstants) ++
        codes.flatMap((_, building) => buildingConstants(building))).distinct
    val constantIndex = constants.zipWithIndex.toMap
    val lookup = MethodHandles.lookup()
    val resolver = ClassHierarchyResolver
      .defaultResolver()
      .orElse(ClassHierarchyResolver.ofClassLoading(getClass.getClassLoader))
    val bytes = ClassFile
      .of(ClassFile.ClassHierarchyResolverOption.of(resolver))
      .build(
        generatedClass,
        (classBuilder: ClassBuilder) =>
          val emitter = Emitter(constantIndex, codeNumbers)
          classBuilder
            .withFlags(ClassFile.ACC_PUBLIC | ClassFile.ACC_FINAL)
            .withInterfaceSymbols(generatedInterface)
          classBuilder.withMethodBody(
            ConstantDescs.INIT_NAME,
            ConstantDescs.MTD_void,
            ClassFile.ACC_PUBLIC,
            (code: CodeBuilder) =>
              code
                .aload(0)
                .invokespecial(
                  objectClass,
                  ConstantDescs.INIT_NAME,
                  ConstantDescs.MTD_void
                )
                .return_()
              ()
          )
          emitter.dispatches(
            classBuilder,
            entries.size,
            program.orientations.size,
            shared.size,
            codes.map((code, _) => codeNumbers(code))
          )
          entries.zipWithIndex.foreach { case ((tree, seedCount), number) =>
            classBuilder.withMethodBody(
              s"entry$number",
              entryType,
              ClassFile.ACC_PUBLIC | ClassFile.ACC_STATIC,
              (code: CodeBuilder) => emitter.entryBody(code, tree, seedCount)
            )
          }
          program.orientations.zipWithIndex.foreach((plan, number) =>
            emitter.buildingMethod(classBuilder, s"added$number", plan.added)
          )
          shared.zipWithIndex.foreach((building, number) =>
            emitter.buildingMethod(classBuilder, s"shared$number", building)
          )
          codes.foreach((code, building) =>
            emitter.buildingMethod(
              classBuilder,
              s"body${codeNumbers(code)}",
              building
            )
          )
      )
    val hidden = lookup.defineHiddenClassWithClassData(
      bytes,
      java.util.List.of(constants*),
      true
    )
    hidden.lookupClass().getDeclaredConstructor().newInstance() match
      case program: GeneratedProgram => program
      case other                     =>
        throw IllegalStateException(
          s"the generated class is no program: $other"
        )

  /** What a step's emission does with the entries it reads: outside a witness,
    * count every entry of a collection into the matching at once; inside one,
    * count each entry tried into the witness's local.
    */
  private enum Mode:
    case Collect
    case Witness(counter: Int)

  /** The locals of an entry's method: its parameters, the matching found so far
    * (a `Searched`), and the slot of each register.
    */
  private final case class SeedFrame(searched: Int, registers: Vector[Int]):
    val graph = 0
    def register(index: Int): Int = registers(index)

  private final class Emitter(
      constantIndex: Map[AnyRef, Int],
      codeNumbers: Map[Code, Int]
  ):

    private def constant(code: CodeBuilder, value: AnyRef): Unit =
      code.ldc(
        DynamicConstantDesc.ofNamed(
          ConstantDescs.BSM_CLASS_DATA_AT,
          ConstantDescs.DEFAULT_NAME,
          constantOf(value),
          Integer.valueOf(constantIndex(value))
        )
      )

    private def integerConstant(code: CodeBuilder, value: Int): Unit =
      code.loadConstant(Integer.valueOf(value))

    private def unboxed(code: CodeBuilder): Unit =
      code.invokestatic(boxes, "unboxToInt", method(integer, objectClass))

    // ---- dispatch ----

    /** The four methods of `GeneratedProgram`, each a switch on its first
      * argument.
      */
    def dispatches(
        classBuilder: ClassBuilder,
        entries: Int,
        orientations: Int,
        shared: Int,
        codes: Vector[Int]
    ): Unit =
      classBuilder.withMethodBody(
        "matches",
        method(matchingClass, integer, graphView, integer),
        ClassFile.ACC_PUBLIC,
        (code: CodeBuilder) =>
          switched(
            code,
            "entry",
            (0 until entries).toVector,
            number =>
              code.aload(2).iload(3)
              code.invokestatic(generatedClass, s"entry$number", entryType)
              code.areturn()
              ()
          )
      )
      buildingDispatch(
        classBuilder,
        "added",
        "orientation",
        (0 until orientations).toVector,
        number => s"added$number"
      )
      buildingDispatch(
        classBuilder,
        "shared",
        "shared subterm",
        (0 until shared).toVector,
        number => s"shared$number"
      )
      buildingDispatch(
        classBuilder,
        "body",
        "code",
        codes,
        number => s"body$number"
      )

    private def buildingDispatch(
        classBuilder: ClassBuilder,
        name: String,
        kind: String,
        numbers: Vector[Int],
        target: Int => String
    ): Unit =
      classBuilder.withMethodBody(
        name,
        method(tupleClass, integer, graphBuilding, vectorClass),
        ClassFile.ACC_PUBLIC,
        (code: CodeBuilder) =>
          switched(
            code,
            kind,
            numbers,
            number =>
              code
                .aload(2)
                .aload(3)
                .invokestatic(generatedClass, target(number), buildingType)
                .areturn()
          )
      )

    /** A switch on the int in local 1: a case for each number, the default
      * throwing.
      */
    private def switched(
        code: CodeBuilder,
        kind: String,
        numbers: Vector[Int],
        body: Int => Unit
    ): Unit =
      val default = code.newLabel()
      val labels = numbers.map(number => (number, code.newLabel()))
      code.iload(1)
      code.lookupswitch(
        default,
        labels.map((number, label) => SwitchCase.of(number, label)).asJava
      )
      labels.foreach((number, label) =>
        code.labelBinding(label)
        body(number)
      )
      code.labelBinding(default)
      code.ldc(kind).iload(1)
      code.invokestatic(
        support,
        "noEntry",
        method(
          described(classOf[RuntimeException]),
          ConstantDescs.CD_String,
          integer
        )
      )
      code.athrow()

    // ---- seeds ----

    /** An entry's method: its tree run from the delta in local 1, the matches
      * handed over grouped by seed.
      */
    def entryBody[C <: NativeSpecializer & Singleton](
        code: CodeBuilder,
        tree: SeedTree[C],
        seedCount: Int
    ): Unit =
      val count = math.max(
        SeedTree.registerCount(tree),
        1 + (0 +: treeSteps(tree).flatMap(registersOf)).max
      )
      val searched = code.allocateLocal(TypeKind.REFERENCE)
      val registers =
        (0 until count).toVector.map(_ => code.allocateLocal(TypeKind.INT))
      val frame = SeedFrame(searched, registers)
      constant(code, GeneratedCodeSupport.searchStarted(seedCount))
      code.astore(searched)
      registers.foreach(slot => code.iconst_m1().istore(slot))
      code.iload(1).istore(frame.register(0))
      val end = code.newLabel()
      treeRun(code, frame, tree, end)
      code.labelBinding(end)
      code.aload(searched)
      code.invokestatic(
        support,
        "searchFinished",
        method(matchingClass, searchedClass)
      )
      code.areturn()

    /** The tree's steps, for every way they succeed, then the matches of the
      * seeds that end there and each branch in turn; then a jump to `failure`,
      * to try the next entry.
      */
    private def treeRun[C <: NativeSpecializer & Singleton](
        code: CodeBuilder,
        frame: SeedFrame,
        tree: SeedTree[C],
        failure: Label
    ): Unit =
      steps(code, frame, tree.steps.toList, failure, Mode.Collect, Right(tree))

    /** The matches of the seeds that end at the tree's node, then each branch,
      * then a jump to `failure`. A branch's steps write only registers its own
      * seeds write after the shared steps, so the registers the next branch
      * reads still hold what the shared steps wrote.
      */
    private def treeEnd[C <: NativeSpecializer & Singleton](
        code: CodeBuilder,
        frame: SeedFrame,
        tree: SeedTree[C],
        failure: Label
    ): Unit =
      tree.ends.foreach(end =>
        code.aload(frame.searched)
        integerConstant(code, end.seed)
        integerConstant(code, end.orientation)
        code.iload(frame.register(end.root))
        code.invokestatic(support, "noBindings", method(vectorClass))
        end.bindings.foreach {
          case Some(register) =>
            code.iload(frame.register(register))
            code.invokestatic(
              support,
              "bound",
              method(vectorClass, vectorClass, integer)
            )
          case None =>
            code.invokestatic(
              support,
              "unbound",
              method(vectorClass, vectorClass)
            )
        }
        code.invokestatic(
          support,
          "found",
          method(
            searchedClass,
            searchedClass,
            integer,
            integer,
            integer,
            vectorClass
          )
        )
        code.astore(frame.searched)
      )
      tree.branches.foreach(branch =>
        val next = code.newLabel()
        treeRun(code, frame, branch, next)
        code.labelBinding(next)
      )
      code.goto_(failure)
      ()

    /** The steps, for every way they succeed, then the finish: a jump to the
      * label of a witness's success (`Left`), or the end of a tree's node
      * (`Right`); a failed step jumps to `failure`. Every path ends in a jump.
      *
      * The finish is an `Either` folded, never matched: the exhaustivity check
      * of a match on a case whose field is a `java.lang.classfile` type loads
      * the library's internal classes, and Scala 3.10.1 fails on them with a
      * CyclicReference (BufferedMethodBuilder, measured on 2026-10-31).
      */
    private def steps[C <: NativeSpecializer & Singleton](
        code: CodeBuilder,
        frame: SeedFrame,
        remaining: List[Step[C]],
        failure: Label,
        mode: Mode,
        finish: Either[Label, SeedTree[C]]
    ): Unit = remaining match
      case Nil =>
        finish.fold(
          label =>
            code.goto_(label)
            ()
          ,
          tree => treeEnd(code, frame, tree, failure)
        )
      case step :: rest =>
        def continued(nextFailure: Label): Unit =
          steps(code, frame, rest, nextFailure, mode, finish)
        step match
          case Step.Layer(node, template, children) =>
            layerRead(code, frame, node, template, children, failure)
            continued(failure)
          case Step.Root(node, target) =>
            code.aload(frame.graph).iload(frame.register(node))
            code.invokeinterface(graphView, "root", method(integer, integer))
            code.istore(frame.register(target))
            continued(failure)
          case Step.Same(first, second) =>
            code
              .iload(frame.register(first))
              .iload(frame.register(second))
              .if_icmpne(failure)
            continued(failure)
          case Step.InstructionIn(instruction, root) =>
            val option = code.allocateLocal(TypeKind.REFERENCE)
            code.aload(frame.graph)
            constant(code, instruction.representation)
            code.invokeinterface(
              graphView,
              "instructionNode",
              method(optionClass, instructionClass)
            )
            code.astore(option)
            code.aload(option).instanceOf(someClass).ifeq(failure)
            code.aload(frame.graph)
            code.aload(option).checkcast(someClass)
            code.invokevirtual(someClass, "value", method(objectClass))
            unboxed(code)
            code.invokeinterface(graphView, "root", method(integer, integer))
            code.iload(frame.register(root)).if_icmpne(failure)
            continued(failure)
          case Step.HasClosure(root) =>
            code.aload(frame.graph).iload(frame.register(root))
            code.invokeinterface(
              graphView,
              "hasClosure",
              method(boolean, integer)
            )
            code.ifeq(failure)
            continued(failure)
          case Step.InstructionNode(instruction, target) =>
            code.aload(frame.graph)
            constant(code, instruction.representation)
            code.invokeinterface(
              graphView,
              "instructionNode",
              method(optionClass, instructionClass)
            )
            nodeFound(code, frame, target, failure)
            continued(failure)
          case Step.Lookup(template, children, target) =>
            code.aload(frame.graph)
            lookedUpLayer(code, frame, template, children)
            code.invokeinterface(
              graphView,
              "layerNode",
              method(optionClass, layerClass)
            )
            nodeFound(code, frame, target, failure)
            continued(failure)
          case Step.EachHeadMember(root, head, target) =>
            eachNode(
              code,
              frame,
              root,
              "headMembers",
              head,
              target,
              failure,
              mode,
              continued
            )
          case Step.EachMember(root, shape, target) =>
            eachNode(
              code,
              frame,
              root,
              "members",
              shape,
              target,
              failure,
              mode,
              continued
            )
          case Step.EachUser(root, role, target) =>
            eachNode(
              code,
              frame,
              root,
              "users",
              role,
              target,
              failure,
              mode,
              continued
            )
          case Step.EachPositionUser(root, role, position, target) =>
            val entries = code.allocateLocal(TypeKind.REFERENCE)
            val size = code.allocateLocal(TypeKind.INT)
            val index = code.allocateLocal(TypeKind.INT)
            val entry = code.allocateLocal(TypeKind.REFERENCE)
            code.aload(frame.graph).iload(frame.register(root))
            constant(code, role)
            code.invokeinterface(
              graphView,
              "positionUsers",
              method(vectorClass, integer, positionRoleClass)
            )
            code.astore(entries)
            loopHead(code, frame, entries, size, index, mode)
            val loop = code.newLabel()
            code.labelBinding(loop)
            code.iload(index).iload(size).if_icmpge(failure)
            code.aload(entries).iload(index)
            code.invokevirtual(
              vectorClass,
              "apply",
              method(objectClass, integer)
            )
            code.checkcast(positionUserClass).astore(entry)
            code.iinc(index, 1)
            counted(code, mode)
            code
              .aload(entry)
              .invokevirtual(positionUserClass, "position", method(integer))
            integerConstant(code, position)
            code.if_icmpne(loop)
            code.aload(frame.graph)
            code
              .aload(entry)
              .invokevirtual(positionUserClass, "user", method(integer))
            code.invokeinterface(graphView, "live", method(boolean, integer))
            code.ifeq(loop)
            code
              .aload(entry)
              .invokevirtual(positionUserClass, "user", method(integer))
            code.istore(frame.register(target))
            continued(loop)
          case Step.Once(inner) =>
            val succeeded = code.newLabel()
            val failed = code.newLabel()
            val (counter, innerMode) = mode match
              case Mode.Collect =>
                val slot = code.allocateLocal(TypeKind.INT)
                code.iconst_0().istore(slot)
                (Some(slot), Mode.Witness(slot))
              case witness: Mode.Witness => (None, witness)
            steps(code, frame, inner.toList, failed, innerMode, Left(succeeded))
            code.labelBinding(succeeded)
            counter.foreach(slot => countRead(code, frame, slot))
            continued(failure)
            code.labelBinding(failed)
            counter.foreach(slot => countRead(code, frame, slot))
            code.goto_(failure)

    /** With an option of a node on the stack: its node to the register, or a
      * jump to `failure` when it is empty.
      */
    private def nodeFound(
        code: CodeBuilder,
        frame: SeedFrame,
        target: Int,
        failure: Label
    ): Unit =
      val option = code.allocateLocal(TypeKind.REFERENCE)
      code.astore(option)
      code.aload(option).instanceOf(someClass).ifeq(failure)
      code.aload(option).checkcast(someClass)
      code.invokevirtual(someClass, "value", method(objectClass))
      unboxed(code)
      code.istore(frame.register(target))

    /** The layer a `Lookup` step looks up, pushed: the template over the nodes
      * at the registers.
      */
    private def lookedUpLayer(
        code: CodeBuilder,
        frame: SeedFrame,
        template: LayerTemplate,
        children: Vector[Int]
    ): Unit = template match
      case LayerTemplate.Apply =>
        require(children.size == 2, s"an application looked up over $children")
        children.foreach(child => code.iload(frame.register(child)))
        code.invokestatic(
          support,
          "applyLayer",
          method(layerClass, integer, integer)
        )
      case LayerTemplate.Parallel =>
        require(children.size == 2, s"a parallel looked up over $children")
        children.foreach(child => code.iload(frame.register(child)))
        code.invokestatic(
          support,
          "parallelLayer",
          method(layerClass, integer, integer)
        )
      case LayerTemplate.Choice =>
        require(children.size == 2, s"a choice looked up over $children")
        children.foreach(child => code.iload(frame.register(child)))
        code.invokestatic(
          support,
          "choiceLayer",
          method(layerClass, integer, integer)
        )
      case LayerTemplate.Thunk(thunkCode, holes) =>
        constant(code, thunkCode)
        constant(code, holes)
        registerVector(code, frame, children)
        code.invokestatic(
          support,
          "thunkLayer",
          method(layerClass, codeIdentifierClass, vectorClass, vectorClass)
        )

    private def registerVector(
        code: CodeBuilder,
        frame: SeedFrame,
        registers: Vector[Int]
    ): Unit =
      code.invokestatic(support, "noNodes", method(vectorClass))
      registers.foreach(register =>
        code.iload(frame.register(register))
        code.invokestatic(
          support,
          "appended",
          method(vectorClass, vectorClass, integer)
        )
      )

    /** The matching with the witness's count of entries read added. */
    private def countRead(
        code: CodeBuilder,
        frame: SeedFrame,
        slot: Int
    ): Unit =
      code.aload(frame.searched).iload(slot)
      code.invokevirtual(searchedClass, "read", method(searchedClass, integer))
      code.astore(frame.searched)

    /** Before an `Each` loop: the size of the entries; outside a witness, every
      * entry counted at once; the index at 0.
      */
    private def loopHead(
        code: CodeBuilder,
        frame: SeedFrame,
        entries: Int,
        size: Int,
        index: Int,
        mode: Mode
    ): Unit =
      code
        .aload(entries)
        .invokevirtual(vectorClass, "length", method(integer))
        .istore(size)
      mode match
        case Mode.Collect    => countRead(code, frame, size)
        case Mode.Witness(_) => ()
      code.iconst_0().istore(index)

    /** Inside a witness, the entry tried counted. */
    private def counted(code: CodeBuilder, mode: Mode): Unit = mode match
      case Mode.Collect          => ()
      case Mode.Witness(counter) => code.iinc(counter, 1)

    private def eachNode(
        code: CodeBuilder,
        frame: SeedFrame,
        root: Int,
        reader: String,
        selector: AnyRef,
        target: Int,
        failure: Label,
        mode: Mode,
        continued: Label => Unit
    ): Unit =
      val entries = code.allocateLocal(TypeKind.REFERENCE)
      val size = code.allocateLocal(TypeKind.INT)
      val index = code.allocateLocal(TypeKind.INT)
      code.aload(frame.graph).iload(frame.register(root))
      constant(code, selector)
      code.invokeinterface(
        graphView,
        reader,
        method(vectorClass, integer, constantOf(selector))
      )
      code.astore(entries)
      loopHead(code, frame, entries, size, index, mode)
      val loop = code.newLabel()
      code.labelBinding(loop)
      code.iload(index).iload(size).if_icmpge(failure)
      code.aload(entries).iload(index)
      code.invokevirtual(vectorClass, "apply", method(objectClass, integer))
      unboxed(code)
      code.istore(frame.register(target))
      code.iinc(index, 1)
      counted(code, mode)
      code.aload(frame.graph).iload(frame.register(target))
      code.invokeinterface(graphView, "live", method(boolean, integer))
      code.ifeq(loop)
      continued(loop)

    /** A `Layer` step: the node's layer has the template's shape (its thunk's
      * code, holes and number of fillings), and its children go to the
      * registers.
      */
    private def layerRead(
        code: CodeBuilder,
        frame: SeedFrame,
        node: Int,
        template: LayerTemplate,
        children: Vector[Int],
        failure: Label
    ): Unit =
      val layer = code.allocateLocal(TypeKind.REFERENCE)
      code.aload(frame.graph).iload(frame.register(node))
      code.invokeinterface(graphView, "layer", method(layerClass, integer))
      code.astore(layer)
      def read(shape: ClassDesc, accessors: Vector[String]): Unit =
        require(
          accessors.size == children.size,
          s"a layer of ${accessors.size} children read into ${children.size} registers"
        )
        code.aload(layer).instanceOf(shape).ifeq(failure)
        accessors
          .zip(children)
          .foreach((accessor, child) =>
            code.aload(layer).checkcast(shape)
            code.invokevirtual(shape, accessor, method(objectClass))
            unboxed(code)
            code.istore(frame.register(child))
          )
      def elements(shape: ClassDesc, accessor: String, count: Int): Unit =
        val vector = code.allocateLocal(TypeKind.REFERENCE)
        code
          .aload(layer)
          .checkcast(shape)
          .invokevirtual(shape, accessor, method(vectorClass))
        code.astore(vector)
        vectorRead(vector, count)
      def vectorRead(vector: Int, count: Int): Unit =
        code.aload(vector).invokevirtual(vectorClass, "length", method(integer))
        integerConstant(code, count)
        code.if_icmpne(failure)
        require(
          count == children.size,
          s"a layer of $count children read into ${children.size} registers"
        )
        children.zipWithIndex.foreach((child, position) =>
          code.aload(vector)
          integerConstant(code, position)
          code.invokevirtual(vectorClass, "apply", method(objectClass, integer))
          unboxed(code)
          code.istore(frame.register(child))
        )
      template match
        case LayerTemplate.Apply =>
          read(applyLayer, Vector("function", "argument"))
        case LayerTemplate.Parallel =>
          read(parallelLayer, Vector("left", "right"))
        case LayerTemplate.Choice => read(choiceLayer, Vector("left", "right"))
        case LayerTemplate.Thunk(thunkCode, holes) =>
          code.aload(layer).instanceOf(thunkLayer).ifeq(failure)
          code
            .aload(layer)
            .checkcast(thunkLayer)
            .invokevirtual(thunkLayer, "code", method(codeIdentifierClass))
          constant(code, thunkCode)
          code.if_acmpne(failure)
          constant(code, holes)
          code
            .aload(layer)
            .checkcast(thunkLayer)
            .invokevirtual(thunkLayer, "holes", method(vectorClass))
          code.invokevirtual(
            objectClass,
            "equals",
            method(boolean, objectClass)
          )
          code.ifeq(failure)
          elements(thunkLayer, "fillings", children.size)

    // ---- buildings ----

    def buildingMethod[C <: NativeSpecializer & Singleton](
        classBuilder: ClassBuilder,
        name: String,
        building: Building[C]
    ): Unit =
      classBuilder.withMethodBody(
        name,
        buildingType,
        ClassFile.ACC_PUBLIC | ClassFile.ACC_STATIC,
        (code: CodeBuilder) =>
          val (graph, node) = built(code, building, 0)
          code.aload(graph).iload(node)
          code.invokestatic(
            support,
            "result",
            method(tupleClass, graphBuilding, integer)
          )
          code.areturn()
          ()
      )

    /** The building emitted from the graph in the local: the locals of the
      * graph after it and of its node, fresh ones written once. Local 1 holds
      * the values.
      */
    private def built[C <: NativeSpecializer & Singleton](
        code: CodeBuilder,
        building: Building[C],
        graph: Int
    ): (Int, Int) =
      building match
        case Building.Value(index) =>
          val node = code.allocateLocal(TypeKind.INT)
          code.aload(1)
          integerConstant(code, index)
          code.invokestatic(
            support,
            "value",
            method(integer, vectorClass, integer)
          )
          code.istore(node)
          (graph, node)
        case Building.InstructionNode(instruction) =>
          code.aload(graph)
          constant(code, instruction.representation)
          code.invokeinterface(
            graphBuilding,
            "instructionAdded",
            method(tupleClass, instructionClass)
          )
          unpacked(code)
        case Building.CodeBody(body) =>
          codeNumbers.get(body) match
            case Some(number) =>
              code.aload(graph).aload(1)
              code.invokestatic(generatedClass, s"body$number", buildingType)
            case None =>
              constant(code, body)
              code.invokestatic(
                support,
                "missingCode",
                method(tupleClass, codeIdentifierClass)
              )
          unpacked(code)
        case Building.Apply(function, argument, readByBeta) =>
          val (withFunction, functionNode) = built(code, function, graph)
          val (withArgument, argumentNode) = built(code, argument, withFunction)
          code.aload(withArgument).iload(functionNode).iload(argumentNode)
          code.invokestatic(
            support,
            "applyLayer",
            method(layerClass, integer, integer)
          )
          val (withApplication, node) = layerAdded(code)
          if readByBeta then
            val afterRead = code.allocateLocal(TypeKind.REFERENCE)
            code.aload(withApplication).iload(node)
            code.invokeinterface(
              graphBuilding,
              "applicationRead",
              method(graphBuilding, integer)
            )
            code.astore(afterRead)
            (afterRead, node)
          else (withApplication, node)
        case Building.Parallel(left, right) =>
          val (withLeft, leftNode) = built(code, left, graph)
          val (withRight, rightNode) = built(code, right, withLeft)
          code.aload(withRight).iload(leftNode).iload(rightNode)
          code.invokestatic(
            support,
            "parallelLayer",
            method(layerClass, integer, integer)
          )
          layerAdded(code)
        case Building.Choice(left, right) =>
          val (withLeft, leftNode) = built(code, left, graph)
          val (withRight, rightNode) = built(code, right, withLeft)
          code.aload(withRight).iload(leftNode).iload(rightNode)
          code.invokestatic(
            support,
            "choiceLayer",
            method(layerClass, integer, integer)
          )
          layerAdded(code)
        case Building.Thunk(thunkCode, holes, fillings) =>
          val (withFillings, nodes) = childrenBuilt(code, fillings, graph)
          code.aload(withFillings)
          constant(code, thunkCode)
          constant(code, holes)
          nodesVector(code, nodes)
          code.invokestatic(
            support,
            "thunkLayer",
            method(layerClass, codeIdentifierClass, vectorClass, vectorClass)
          )
          layerAdded(code)

    private def childrenBuilt[C <: NativeSpecializer & Singleton](
        code: CodeBuilder,
        buildings: Vector[Building[C]],
        graph: Int
    ): (Int, Vector[Int]) =
      buildings.foldLeft((graph, Vector.empty[Int])) {
        case ((current, nodes), building) =>
          val (next, node) = built(code, building, current)
          (next, nodes :+ node)
      }

    private def nodesVector(code: CodeBuilder, nodes: Vector[Int]): Unit =
      code.invokestatic(support, "noNodes", method(vectorClass))
      nodes.foreach(node =>
        code.iload(node)
        code.invokestatic(
          support,
          "appended",
          method(vectorClass, vectorClass, integer)
        )
      )

    /** With a graph and a layer on the stack: the layer added. */
    private def layerAdded(code: CodeBuilder): (Int, Int) =
      code.invokeinterface(
        graphBuilding,
        "layerAdded",
        method(tupleClass, layerClass)
      )
      unpacked(code)

    /** With a tuple of a graph and a node on the stack: both stored in fresh
      * locals.
      */
    private def unpacked(code: CodeBuilder): (Int, Int) =
      val tuple = code.allocateLocal(TypeKind.REFERENCE)
      val graph = code.allocateLocal(TypeKind.REFERENCE)
      val node = code.allocateLocal(TypeKind.INT)
      code.astore(tuple)
      code.aload(tuple).invokevirtual(tupleClass, "_1", method(objectClass))
      code.checkcast(graphBuilding).astore(graph)
      code.aload(tuple).invokevirtual(tupleClass, "_2", method(objectClass))
      unboxed(code)
      code.istore(node)
      (graph, node)
