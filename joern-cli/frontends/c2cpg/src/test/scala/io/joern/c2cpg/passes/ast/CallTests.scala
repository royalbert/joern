package io.joern.c2cpg.passes.ast

import io.joern.c2cpg.astcreation.Defines
import io.joern.c2cpg.testfixtures.C2CpgSuite
import io.joern.x2cpg.Defines as X2CpgDefines
import io.shiftleft.codepropertygraph.generated.{DispatchTypes, Operators}
import io.shiftleft.codepropertygraph.generated.nodes.Call
import io.shiftleft.codepropertygraph.generated.nodes.Identifier
import io.shiftleft.codepropertygraph.generated.nodes.Literal
import io.shiftleft.semanticcpg.language.*

class CallTests extends C2CpgSuite {

  implicit val resolver: NoResolve.type = NoResolve

  "CallTest 1" should {
    val cpg = code("""
        |int add(int x, int y) {
        |  return x + y;
        |}
        |int main(int argc, char **argv) {
        |  printf("%d\n", add((1+2), 3));
        |}""".stripMargin)

    "contain a call node for `add` with correct fields" in {
      val List(x) = cpg.call("add").l
      x.code shouldBe "add((1+2), 3)"
      x.name shouldBe "add"
      x.order shouldBe 2
      x.methodFullName shouldBe "add"
      x.argumentIndex shouldBe 2
      // TODO x.signature
      // x.typeFullName : deprecated
      x.lineNumber shouldBe Option(6)
      x.columnNumber shouldBe Option(18)
    }

    "allow traversing from call to arguments" in {
      cpg.call("add").argument.size shouldBe 2

      val List(arg1) = cpg.call("add").argument(1).l
      arg1.isInstanceOf[Call] shouldBe true
      arg1.asInstanceOf[Call].name shouldBe Operators.addition
      arg1.code shouldBe "1+2"
      arg1.order shouldBe 1
      arg1.argumentIndex shouldBe 1

      val List(arg2) = cpg.call("add").argument(2).l
      arg2.isInstanceOf[Literal] shouldBe true
      arg2.asInstanceOf[Literal].code shouldBe "3"
      arg2.code shouldBe "3"
      arg2.order shouldBe 2
      arg2.argumentIndex shouldBe 2
    }

    "allow traversing from call to surrounding method" in {
      val List(x) = cpg.call("add").method.l
      x.name shouldBe "main"
    }

    "allow traversing from call to callee method" in {
      val List(x) = cpg.call("add").callee.l
      x.name shouldBe "add"
    }

    "allow traversing from argument to parameter" in {
      val List(x) = cpg.call("add").argument(1).parameter.l
      x.name shouldBe "x"
    }
  }

  "CallTest 2" should {
    val cpg = code(
      """
        |using namespace std;
        |
        |class A{
        |  public:
        |    int a;
        |};
        |
        |class B{
        |  public:
        |    A* GetObj();
        |};
        |
        |A* B::GetObj() {
        |  return nullptr;
        |}
        |
        |class C{
        |  public:
        |    A* GetObject();
        |};
        |
        |A* C::GetObject() {
        |  B * b;
        |  return b->GetObj();
        |}
        |
        |bool Run(A *obj, C *c) {
        |  const A * a = c->GetObject();
        |  a->a;
        |  return true;
        |}
        |""".stripMargin,
      "code.cpp"
    )

    "have the correct callIn" in {
      val List(m) = cpg.method.nameNot("<global>").where(_.ast.isReturn.code(".*nullptr.*")).l
      val List(c) = cpg.call.codeExact("b->GetObj()").l
      c.callee.l should contain(m)
      val List(callIn) = m.callIn.l
      callIn.code shouldBe "b->GetObj()"
    }
  }

  "CallTest 3" should {
    val cpg = code(
      """
        |int square(int num) {
        |    return num * num;
        |}
        |void call_square() {
        |    ::square(10);
        |}
        |""".stripMargin,
      "test.cpp"
    )
    "have correct names for static methods / calls" in {
      cpg.method.name("square").fullName.head shouldBe "square:int(int)"
      cpg.method.name("call_square").call.methodFullName.head shouldBe "square:int(int)"
    }
  }

  "CallTest 4" should {
    val cpg = code(
      """
        |class A {
        |  public:
        |    static int square(int num) {
        |      return num * num;
        |    }
        |};
        |
        |void call_square() {
        |  A::square(10);
        |}
        |""".stripMargin,
      "test.cpp"
    )
    "have correct names for static methods / calls from classes" in {
      cpg.method.name("square").fullName.head shouldBe "A.square:int(int)"
      cpg.method.name("call_square").call.methodFullName.head shouldBe "A.square:int(int)"
    }
  }

  "CallTest 5" should {
    val cpg = code(
      """
        |class A {
        |  void a() {
        |    b();
        |  }
        |  void b() {}
        |};
        |""".stripMargin,
      "test.cpp"
    )
    "have correct type full names for calls" in {
      val List(bCall) = cpg.call.l
      bCall.methodFullName shouldBe "A.b:void()"
      val List(bMethod) = cpg.method.name("b").internal.l
      bMethod.fullName shouldBe "A.b:void()"
      bMethod.callIn.head shouldBe bCall
      bCall.callee.head shouldBe bMethod
    }
  }

  "CallTest 6" should {
    val cpg = code(
      """
        |class A {
        |  public:
        |    void foo1(){
        |      foo2();
        |    }
        |	static void foo2() {}
        |};
        |
        |int main() {
        |  A a;
        |  a.foo1();
        |}
        |""".stripMargin,
      "test.cpp"
    )
    "have correct type full names for calls" in {
      val List(foo2Call) = cpg.call("foo2").l
      foo2Call.methodFullName shouldBe "A.foo2:void()"
      val List(foo2Method) = cpg.method("foo2").l
      foo2Method.fullName shouldBe "A.foo2:void()"
    }
  }

  "Successfully typed calls" should {
    "have correct call for call on non virtual class method" in {
      val cpg = code(
        """
          |namespace NNN {
          |  class A {
          |    public:
          |      void foo(int a){}
          |  };
          |}
          |
          |void outer() {
          |  NNN::A a;
          |  a.foo(1);
          |}
          |""".stripMargin,
        "test.cpp"
      )

      val List(call) = cpg.call.nameExact("foo").l
      call.signature shouldBe "void(int)"
      call.methodFullName shouldBe "NNN.A.foo:void(int)"
      call.dispatchType shouldBe DispatchTypes.STATIC_DISPATCH
      call.typeFullName shouldBe "void"

      val List(instArg, arg1) = call.argument.l
      instArg.code shouldBe "a"
      instArg.argumentIndex shouldBe 0
      arg1.code shouldBe "1"
      arg1.argumentIndex shouldBe 1

      call.receiver.isEmpty shouldBe true
    }

    "have correct call for call on virtual class method" in {
      val cpg = code(
        """
          |namespace NNN {
          |  class A {
          |    public:
          |      virtual void foo(int a){}
          |  };
          |}
          |
          |void outer() {
          |  NNN::A a;
          |  a.foo(1);
          |}
          |""".stripMargin,
        "test.cpp"
      )

      val List(call) = cpg.call.nameExact("foo").l
      call.signature shouldBe "void(int)"
      call.methodFullName shouldBe "NNN.A.foo:void(int)"
      call.dispatchType shouldBe DispatchTypes.DYNAMIC_DISPATCH
      call.typeFullName shouldBe "void"

      val List(instArg, arg1) = call.argument.l
      instArg.code shouldBe "a"
      instArg.argumentIndex shouldBe 0
      arg1.code shouldBe "1"
      arg1.argumentIndex shouldBe 1

      val List(receiver) = call.receiver.l
      receiver shouldBe instArg
    }

    "have correct call for call on stand alone method (CPP)" in {
      val cpg = code(
        """
          |namespace NNN {
          |  void foo(int a){}
          |}
          |
          |void outer() {
          |  NNN::foo(1);
          |}
          |""".stripMargin,
        "test.cpp"
      )

      val List(call) = cpg.call.nameExact("foo").l
      call.signature shouldBe "void(int)"
      call.methodFullName shouldBe "NNN.foo:void(int)"
      call.dispatchType shouldBe DispatchTypes.STATIC_DISPATCH
      call.typeFullName shouldBe "void"

      val List(arg1) = call.argument.l
      arg1.code shouldBe "1"

      call.receiver.isEmpty shouldBe true
    }

    "have correct call for call on lambda function with explicit return type" in {
      val cpg = code(
        """
          |void outer() {
          |  [](int a) -> int { return a; }(1);
          |}
          |""".stripMargin,
        "test.cpp"
      )

      val List(call) = cpg.call.nameExact("<operator>()").l
      call.signature shouldBe "int(int)"
      call.methodFullName shouldBe "<operator>():int(int)"
      call.dispatchType shouldBe DispatchTypes.DYNAMIC_DISPATCH
      call.typeFullName shouldBe "int"

      val List(arg1) = call.argument.l
      arg1.code shouldBe "1"
      arg1.argumentIndex shouldBe 1

      val List(receiver) = call.receiver.l
      receiver.isMethodRef shouldBe true
      receiver.argumentIndex shouldBe -1
    }

    "have correct call for call on lambda function without explicit return type" in {
      val cpg = code(
        """
          |void outer() {
          |  [](int a) {}(1);
          |}
          |""".stripMargin,
        "test.cpp"
      )

      val List(call) = cpg.call.nameExact("<operator>()").l
      call.signature shouldBe "void(int)"
      call.methodFullName shouldBe "<operator>():void(int)"
      call.dispatchType shouldBe DispatchTypes.DYNAMIC_DISPATCH
      call.typeFullName shouldBe "void"

      val List(arg1) = call.argument.l
      arg1.code shouldBe "1"
      arg1.argumentIndex shouldBe 1

      val List(receiver) = call.receiver.l
      receiver.isMethodRef shouldBe true
      receiver.argumentIndex shouldBe -1
    }

    "have correct call for call on function pointer (CPP)" in {
      val cpg = code(
        """
          |class A {
          |  public:
          |    void (*foo)(int);
          |};
          |
          |void outer() {
          |  A a;
          |  a.foo(1);
          |}
          |""".stripMargin,
        "test.cpp"
      )

      val List(call) = cpg.call.nameExact(Defines.OperatorPointerCall).l
      call.signature shouldBe ""
      call.methodFullName shouldBe Defines.OperatorPointerCall
      call.dispatchType shouldBe DispatchTypes.DYNAMIC_DISPATCH
      call.typeFullName shouldBe "void"

      val List(arg1) = call.argument.l
      arg1.code shouldBe "1"
      arg1.argumentIndex shouldBe 1

      val List(receiver) = call.receiver.l
      receiver.code shouldBe "a.foo"
      receiver.argumentIndex shouldBe -1
    }

    "have correct call for call on callable object" in {
      val cpg = code(
        """
          |namespace NNN {
          |  class Callable {
          |    public:
          |      void operator()(int a){}
          |  };
          |}
          |class A {
          |  public:
          |    NNN::Callable foo;
          |};
          |
          |void outer() {
          |  A a;
          |  a.foo(1);
          |}
          |""".stripMargin,
        "test.cpp"
      )

      val List(call) = cpg.call.nameExact("()").l
      call.signature shouldBe "void(int)"
      call.methodFullName shouldBe "NNN.Callable.():void(int)"
      call.dispatchType shouldBe DispatchTypes.STATIC_DISPATCH
      call.typeFullName shouldBe "void"

      val List(instArg, arg1) = call.argument.l
      instArg.code shouldBe "a.foo"
      instArg.argumentIndex shouldBe 0
      arg1.code shouldBe "1"
      arg1.argumentIndex shouldBe 1

      val List(receiver) = call.receiver.l
      receiver shouldBe instArg
    }

    "have correct call for call on a cv-qualified callable object" in {
      val cpg = code(
        """
          |struct Cmp {
          |  bool operator()(int a, int b) const { return a < b; }
          |};
          |bool viaValue(Cmp c) { return c(1, 2); }
          |bool viaConstValue(const Cmp c) { return c(1, 2); }
          |bool viaConstRef(const Cmp &c) { return c(1, 2); }
          |bool viaConstPtr(const Cmp *c) { return (*c)(1, 2); }
          |""".stripMargin,
        "test.cpp"
      )

      val calls = cpg.call.nameExact("()").l
      calls.size shouldBe 4
      calls.map(_.methodFullName).distinct shouldBe List("Cmp.():bool(int,int)<const>")
      calls.map(_.signature).distinct shouldBe List("bool(int,int)<const>")
      calls.flatMap(_.callee.isExternal.l).distinct shouldBe List(false)
      calls.map(_.dispatchType).distinct shouldBe List(DispatchTypes.STATIC_DISPATCH)
      calls.map(_.typeFullName).distinct shouldBe List("bool")

      calls.foreach { call =>
        inside(call.argument.l) { case List(instArg, arg1, arg2) =>
          instArg.argumentIndex shouldBe 0
          arg1.code shouldBe "1"
          arg2.code shouldBe "2"
          call.receiver.l shouldBe List(instArg)
        }
      }
      calls.argument.argumentIndex(0).code.l.sorted shouldBe List("*c", "c", "c", "c")
    }

    "have correct call for call on a const lambda" in {
      val cpg = code(
        """
          |void foo() {
          |  const auto x = [](int n) -> int { return n; };
          |  x(10);
          |}
          |""".stripMargin,
        "test.cpp"
      )

      inside(cpg.call.nameExact("<operator>()").l) { case List(call) =>
        call.methodFullName shouldBe "<operator>():int(int)"
        call.signature shouldBe "int(int)"
        call.dispatchType shouldBe DispatchTypes.DYNAMIC_DISPATCH
        inside(call.receiver.l) { case List(receiver: Identifier) =>
          receiver.code shouldBe "x"
        }
        inside(call.argument.l) { case List(lit: Literal) =>
          lit.code shouldBe "10"
        }
      }
    }

    "have correct call for call on function pointer (C)" in {
      val cpg = code(
        """
          |struct A {
          |  void (*foo)(int);
          |}
          |void outer() {
          |  struct A a;
          |  a.foo(1);
          |}
          |""".stripMargin,
        "test.c"
      )

      val List(call) = cpg.call.nameExact(Defines.OperatorPointerCall).l
      call.signature shouldBe ""
      call.methodFullName shouldBe Defines.OperatorPointerCall
      call.dispatchType shouldBe DispatchTypes.DYNAMIC_DISPATCH
      call.typeFullName shouldBe "void"

      val List(arg1) = call.argument.l
      arg1.code shouldBe "1"
      arg1.argumentIndex shouldBe 1

      val List(receiver) = call.receiver.l
      receiver.code shouldBe "a.foo"
      receiver.argumentIndex shouldBe -1
    }

    "have correct call for call on stand alone method (C)" in {
      val cpg = code(
        """
          |void foo(int) {}
          |void outer() {
          |  foo(1);
          |}
          |""".stripMargin,
        "test.c"
      )

      val List(call) = cpg.call.nameExact("foo").l
      call.signature shouldBe ""
      call.methodFullName shouldBe "foo"
      call.dispatchType shouldBe DispatchTypes.STATIC_DISPATCH
      call.typeFullName shouldBe "void"

      val List(arg1) = call.argument.l
      arg1.code shouldBe "1"

      call.receiver.isEmpty shouldBe true
    }

    "have correct call for call on extern C function" in {
      val cpg = code(
        """
          |extern "C" {
          |  void foo(int);
          |}
          |
          |void outer() {
          |  foo(1);
          |}
          |""".stripMargin,
        "test.cpp"
      )

      val List(call) = cpg.call.nameExact("foo").l
      call.signature shouldBe ""
      call.methodFullName shouldBe "foo"
      call.dispatchType shouldBe DispatchTypes.STATIC_DISPATCH
      call.typeFullName shouldBe "void"

      val List(arg1) = call.argument.l
      arg1.code shouldBe "1"
      arg1.argumentIndex shouldBe 1

      call.receiver.isEmpty shouldBe true
    }
  }

  "Not successfully typed calls" should {
    "have correct call for field reference style call (CPP)" in {
      val cpg = code(
        """
          |void outer() {
          |  Unknown a;
          |  a.foo(1);
          |}
          |""".stripMargin,
        "test.cpp"
      )

      val List(call) = cpg.call.nameExact("foo").l
      call.signature shouldBe X2CpgDefines.UnresolvedSignature
      call.methodFullName shouldBe s"${X2CpgDefines.UnresolvedNamespace}.foo:${X2CpgDefines.UnresolvedSignature}(1)"
      call.dispatchType shouldBe DispatchTypes.STATIC_DISPATCH
      call.typeFullName shouldBe X2CpgDefines.Any

      val List(instArg, arg1) = call.argument.l
      instArg.code shouldBe "a"
      instArg.argumentIndex shouldBe 0
      arg1.code shouldBe "1"
      arg1.argumentIndex shouldBe 1

      val List(receiver) = call.receiver.l
      receiver shouldBe instArg
    }

    "have correct call for plain call (CPP)" in {
      val cpg = code(
        """
          |void outer() {
          |  foo(1);
          |}
          |""".stripMargin,
        "test.cpp"
      )

      val List(call) = cpg.call.nameExact("foo").l
      call.signature shouldBe X2CpgDefines.UnresolvedSignature
      call.methodFullName shouldBe s"${X2CpgDefines.UnresolvedNamespace}.foo:${X2CpgDefines.UnresolvedSignature}(1)"
      call.dispatchType shouldBe DispatchTypes.STATIC_DISPATCH
      call.typeFullName shouldBe X2CpgDefines.Any

      val List(arg1) = call.argument.l
      arg1.code shouldBe "1"
      arg1.argumentIndex shouldBe 1

      call.receiver.isEmpty shouldBe true
    }

    "have correct call for call on arbitrary expression (CPP)" in {
      val cpg = code(
        """
          |void outer() {
          |  getX()(1);
          |}
          |""".stripMargin,
        "test.cpp"
      )

      val List(call) = cpg.call.nameExact("<operator>()").l
      call.signature shouldBe X2CpgDefines.UnresolvedSignature
      call.methodFullName shouldBe s"${X2CpgDefines.UnresolvedNamespace}.<operator>():${X2CpgDefines.UnresolvedSignature}(1)"
      call.dispatchType shouldBe DispatchTypes.STATIC_DISPATCH
      call.typeFullName shouldBe X2CpgDefines.Any

      val List(instArg, arg1) = call.argument.l
      instArg.code shouldBe "getX()"
      instArg.argumentIndex shouldBe 0
      arg1.code shouldBe "1"
      arg1.argumentIndex shouldBe 1

      val List(receiver) = call.receiver.l
      receiver shouldBe instArg
    }

    "have correct call for field reference style call (C)" in {
      val cpg = code(
        """
          |void outer() {
          |  struct A a;
          |  a.foo(1);
          |}
          |""".stripMargin,
        "test.c"
      )

      val List(call) = cpg.call.nameExact(Defines.OperatorPointerCall).l
      call.signature shouldBe ""
      call.methodFullName shouldBe Defines.OperatorPointerCall
      call.dispatchType shouldBe DispatchTypes.DYNAMIC_DISPATCH
      call.typeFullName shouldBe X2CpgDefines.Any

      val List(arg1) = call.argument.l
      arg1.code shouldBe "1"
      arg1.argumentIndex shouldBe 1

      val List(receiver) = call.receiver.l
      receiver.code shouldBe "a.foo"
      receiver.argumentIndex shouldBe -1
    }

    "have correct call for plain call (C)" in {
      val cpg = code(
        """
          |void outer() {
          |  foo(1);
          |}
          |""".stripMargin,
        "test.c"
      )

      val List(call) = cpg.call.nameExact("foo").l
      call.signature shouldBe ""
      call.methodFullName shouldBe s"foo"
      call.dispatchType shouldBe DispatchTypes.STATIC_DISPATCH
      call.typeFullName shouldBe X2CpgDefines.Any

      val List(arg1) = call.argument.l
      arg1.code shouldBe "1"
      arg1.argumentIndex shouldBe 1

      call.receiver.isEmpty shouldBe true
    }

    "have correct call for call on arbitrary expression (C)" in {
      val cpg = code(
        """
          |void outer() {
          |  getX()(1);
          |}
          |""".stripMargin,
        "test.c"
      )

      val List(call) = cpg.call.nameExact(Defines.OperatorPointerCall).l
      call.signature shouldBe ""
      call.methodFullName shouldBe Defines.OperatorPointerCall
      call.dispatchType shouldBe DispatchTypes.DYNAMIC_DISPATCH
      call.typeFullName shouldBe X2CpgDefines.Any

      val List(arg1) = call.argument.l
      arg1.code shouldBe "1"
      arg1.argumentIndex shouldBe 1

      val List(receiver) = call.receiver.l
      receiver.code shouldBe "getX()"
      receiver.argumentIndex shouldBe -1
    }
  }

  "Overloaded operator calls" should {

    "link an implicit operator() call to its declaration" in {
      val cpg = code(
        """
          |struct Fn {
          |  int operator()(int a) { return a * 2; }
          |};
          |int main() {
          |  Fn f;
          |  return f(21);
          |}
          |""".stripMargin,
        "test.cpp"
      )
      val List(method) = cpg.typeDecl.nameExact("Fn").method.l
      method.name shouldBe "()"
      method.fullName shouldBe "Fn.():int(int)"
      method.isExternal shouldBe false

      val List(call) = cpg.call.codeExact("f(21)").l
      call.name shouldBe method.name
      call.methodFullName shouldBe method.fullName
      call.signature shouldBe "int(int)"
      call.dispatchType shouldBe DispatchTypes.STATIC_DISPATCH
      call.typeFullName shouldBe "int"

      call.callee.l shouldBe List(method)
      method.callIn.l shouldBe List(call)
      // no external stub is synthesised for the unmatched spelling any more
      cpg.method.fullNameExact("Fn.<operator>():int(int)").l shouldBe empty
    }

    "link an explicitly named operator() call to its declaration" in {
      val cpg = code(
        """
          |struct Fn {
          |  int operator()(int a) { return a * 2; }
          |};
          |int main() {
          |  Fn f;
          |  return f.operator()(21);
          |}
          |""".stripMargin,
        "test.cpp"
      )
      val List(method) = cpg.typeDecl.nameExact("Fn").method.l
      method.fullName shouldBe "Fn.():int(int)"

      val List(call) = cpg.call.codeExact("f.operator()(21)").l
      call.name shouldBe "()"
      call.methodFullName shouldBe method.fullName
      call.signature shouldBe "int(int)"

      call.callee.l shouldBe List(method)
      method.callIn.l shouldBe List(call)
    }

    "link explicitly named operator+ and operator[] calls to their declarations" in {
      val cpg = code(
        """
          |struct Fn {
          |  int operator+(const Fn& o) const { return 1; }
          |  int operator[](int i) { return i; }
          |};
          |int main() {
          |  Fn f;
          |  return f.operator+(f) + f.operator[](3);
          |}
          |""".stripMargin,
        "test.cpp"
      )
      val List(plus, index) = cpg.typeDecl.nameExact("Fn").method.l
      plus.fullName shouldBe "Fn.+:int(Fn&)<const>"
      index.fullName shouldBe "Fn.[]:int(int)"

      val List(plusCall) = cpg.call.codeExact("f.operator+(f)").l
      plusCall.name shouldBe "+"
      plusCall.methodFullName shouldBe plus.fullName
      plusCall.callee.l shouldBe List(plus)

      val List(indexCall) = cpg.call.codeExact("f.operator[](3)").l
      indexCall.name shouldBe "[]"
      indexCall.methodFullName shouldBe index.fullName
      indexCall.callee.l shouldBe List(index)
    }

    "link an explicitly named free operator call to its declaration" in {
      val cpg = code(
        """
          |struct A {
          |  int v;
          |};
          |int operator+(const A& l, const A& r) { return l.v + r.v; }
          |int main() {
          |  A a, b;
          |  return operator+(a, b);
          |}
          |""".stripMargin,
        "test.cpp"
      )
      val List(method) = cpg.method.nameExact("+").l
      method.fullName shouldBe "+:int(A&,A&)"
      method.isExternal shouldBe false

      val List(call) = cpg.call.codeExact("operator+(a, b)").l
      call.name shouldBe "+"
      call.methodFullName shouldBe method.fullName
      call.callee.l shouldBe List(method)
      method.callIn.l shouldBe List(call)
    }

  }

  "Calls to C++ functions whose parameter types are typedefs" should {

    "link to the function's definition" in {
      val cpg = code(
        """
          |typedef unsigned short u16;
          |typedef struct s { int x; } S;
          |namespace std { typedef unsigned long size_t; }
          |int plain(u16 a) { return a; }
          |int sized(std::size_t n) { return (int)n; }
          |int pointer(S *p) { return p->x; }
          |int main() {
          |  S v;
          |  return plain(1) + sized(2) + pointer(&v);
          |}
          |""".stripMargin,
        "test.cpp"
      )
      List("plain" -> "plain:int(u16)", "sized" -> "sized:int(std.size_t)", "pointer" -> "pointer:int(S*)").foreach {
        case (name, fullName) =>
          withClue(name) {
            cpg.method.nameExact(name).fullName.l shouldBe List(fullName)
            inside(cpg.call.nameExact(name).l) { case List(call) =>
              call.methodFullName shouldBe fullName
              call.signature shouldBe fullName.substring(fullName.indexOf(':') + 1)
              call.callee.isExternal.l shouldBe List(false)
            }
          }
      }
    }

    "link to the definition of a function in a namespace" in {
      val cpg = code(
        """
          |namespace n {
          |  typedef int T;
          |  int declaredInside(T v);
          |  int definedInside(T v) { return v; }
          |}
          |int n::declaredInside(T v) { return v; }
          |int main() { return n::declaredInside(1) + n::definedInside(2); }
          |""".stripMargin,
        "test.cpp"
      )
      List("declaredInside" -> "n.declaredInside:int(n.T)", "definedInside" -> "n.definedInside:int(n.T)").foreach {
        case (name, fullName) =>
          withClue(name) {
            cpg.method.nameExact(name).fullName.l shouldBe List(fullName)
            cpg.call.nameExact(name).methodFullName.l shouldBe List(fullName)
            cpg.call.nameExact(name).callee.isExternal.l shouldBe List(false)
          }
      }
    }

    "link to the definition of a method" in {
      val cpg = code(
        """
          |typedef unsigned short u16;
          |struct Box {
          |  int value;
          |  int set(u16 v) { value = v; return value; }
          |  int get(u16 v);
          |  int twice(u16 v) { return set(v) + set(v); }
          |  static int make(u16 v) { return v; }
          |  int operator()(u16 v) { return v; }
          |};
          |int Box::get(u16 v) { return value + v; }
          |int main() {
          |  Box b;
          |  return b.set(1) + b.get(2) + b.twice(3) + Box::make(4) + b(5);
          |}
          |""".stripMargin,
        "test.cpp"
      )
      List(
        "set"   -> ("Box.set:int(u16)", 3),
        "get"   -> ("Box.get:int(u16)", 1),
        "twice" -> ("Box.twice:int(u16)", 1),
        "make"  -> ("Box.make:int(u16)", 1),
        "()"    -> ("Box.():int(u16)", 1)
      ).foreach { case (name, (fullName, callCount)) =>
        withClue(name) {
          cpg.method.nameExact(name).fullName.l shouldBe List(fullName)
          cpg.call.nameExact(name).methodFullName.l shouldBe List.fill(callCount)(fullName)
          cpg.call.nameExact(name).callee.isExternal.l shouldBe List.fill(callCount)(false)
        }
      }
    }

    "link to the definition when the function is declared in a header and defined in another file" in {
      val cpg = code(
        """
          |typedef unsigned int u32;
          |int api(u32 v);
          |""".stripMargin,
        "api.h"
      ).moreCode(
        """
          |#include "api.h"
          |int api(u32 v) { return v; }
          |""".stripMargin,
        "api.cpp"
      ).moreCode(
        """
          |#include "api.h"
          |int main() { return api(1); }
          |""".stripMargin,
        "main.cpp"
      )
      cpg.method.nameExact("api").fullName.l shouldBe List("api:int(u32)")
      inside(cpg.call.nameExact("api").l) { case List(call) =>
        call.methodFullName shouldBe "api:int(u32)"
        call.callee.filename.l shouldBe List("api.cpp")
      }
    }
  }

  "Calls to C++ constructors whose parameter types are typedefs" should {
    val cpg = code(
      """
        |typedef int (*Callback)(int);
        |struct Interpreter {
        |  Callback cb;
        |  Interpreter(Callback aCallback) : cb(aCallback) {}
        |};
        |namespace ns {
        |  struct Base {
        |    Base(Callback c) {}
        |  };
        |}
        |struct Derived : ns::Base {
        |  Derived(Callback c) : ns::Base(c) {}
        |};
        |struct Lazy {
        |  Lazy(Callback c = 0) {}
        |};
        |struct Member {
        |  Member() = delete;
        |  Member(Callback c) {}
        |};
        |struct Holder {
        |  Member member;
        |  Holder(Callback c) : member(c) {}
        |};
        |typedef Interpreter Interp;
        |int id(int x) { return x; }
        |void use() {
        |  Callback c = id;
        |  Interpreter direct(c);
        |  Interpreter braced{c};
        |  Interpreter *allocated = new Interpreter(c);
        |  Interpreter temporary = Interpreter{c};
        |  Interp aliased(c);
        |  Derived derived(c);
        |  Lazy defaulted;
        |}
        |""".stripMargin,
      "test.cpp"
    )

    "link to the constructor" in {
      List(
        "Interpreter.Interpreter(c)" -> ("Interpreter.Interpreter:void(Callback)", 2),
        "new Interpreter(c)"         -> ("Interpreter.Interpreter:void(Callback)", 1),
        "Interpreter{c}"             -> ("Interpreter.Interpreter:void(Callback)", 1),
        "Interp.Interp(c)"           -> ("Interpreter.Interpreter:void(Callback)", 1),
        "Derived.Derived(c)"         -> ("Derived.Derived:void(Callback)", 1),
        "ns::Base(c)"                -> ("ns.Base.Base:void(Callback)", 1),
        "Lazy.Lazy()"                -> ("Lazy.Lazy:void(Callback)", 1)
      ).foreach { case (callCode, (fullName, callCount)) =>
        withClue(callCode) {
          cpg.method.fullNameExact(fullName).isExternal.l shouldBe List(false)
          val calls = cpg.call.codeExact(callCode).nameNot(Operators.assignment, Defines.OperatorNew).l
          calls.map(_.methodFullName) shouldBe List.fill(callCount)(fullName)
          calls.map(_.signature) shouldBe List.fill(callCount)("void(Callback)")
          calls.flatMap(_.callee.isExternal.l) shouldBe List.fill(callCount)(false)
        }
      }
    }

    "not name a call after a deleted constructor" in {
      cpg.call.methodFullNameExact("Member.Member:void()").l shouldBe empty
    }
  }

  "Calls to C++ functions whose declarations spell a parameter type differently from the function's type" should {
    val cpg = code(
      """
        |int none(void) { return 1; }
        |int volatileValue(volatile int v) { return v; }
        |int array(int a[4]) { return a[0]; }
        |int main() {
        |  int arr[4] = {0};
        |  return none() + volatileValue(1) + array(arr);
        |}
        |""".stripMargin,
      "test.cpp"
    )

    "link to the function's definition" in {
      List("none", "volatileValue", "array").foreach { name =>
        withClue(name) {
          inside(cpg.method.nameExact(name).l) { case List(method) =>
            inside(cpg.call.nameExact(name).l) { case List(call) =>
              call.methodFullName shouldBe method.fullName
              call.callee.l shouldBe List(method)
            }
          }
        }
      }
    }
  }

  "Calls to C++ member functions that the object's class inherits" should {
    "link to the method of the base class that declares it" in {
      val cpg = code(
        """
          |struct Base { void stop() {} virtual void fire() {} int operator()(int v) { return v; } };
          |struct Mid : Base { void start(int d) {} };
          |struct Leaf : Mid {};
          |template <typename T> struct Tpl { void tb() {} };
          |struct FromTpl : Tpl<int> {};
          |namespace ns { namespace { struct Hidden { void hm() {} }; } struct FromHidden : Hidden {}; }
          |void use(Leaf &l, Mid *m, FromTpl t, ns::FromHidden h) {
          |  l.stop(); m->stop(); l.start(1); l.fire(); l(2); t.tb(); h.hm();
          |}
          |""".stripMargin,
        "test.cpp"
      )
      List(
        "stop"  -> ("Base.stop:void()", 2),
        "start" -> ("Mid.start:void(int)", 1),
        "fire"  -> ("Base.fire:void()", 1),
        "()"    -> ("Base.():int(int)", 1),
        "tb"    -> ("Tpl.tb:void()", 1),
        "hm"    -> ("ns.Hidden.hm:void()", 1)
      ).foreach { case (name, (fullName, callCount)) =>
        withClue(name) {
          cpg.method.nameExact(name).fullName.l shouldBe List(fullName)
          cpg.call.nameExact(name).methodFullName.l shouldBe List.fill(callCount)(fullName)
          cpg.call.nameExact(name).callee.isExternal.l shouldBe List.fill(callCount)(false)
        }
      }
    }
  }
}
