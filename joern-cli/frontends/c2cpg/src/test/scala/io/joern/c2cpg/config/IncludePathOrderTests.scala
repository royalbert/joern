package io.joern.c2cpg.config

import io.joern.c2cpg.Config
import io.joern.c2cpg.Frontend
import io.joern.c2cpg.testfixtures.C2CpgSuite
import io.joern.x2cpg.X2Cpg
import io.shiftleft.semanticcpg.language.*
import io.shiftleft.semanticcpg.utils.FileUtil
import io.shiftleft.semanticcpg.utils.FileUtil.*

import java.nio.file.Files

class IncludePathOrderTests extends C2CpgSuite {

  "Include directories given as --include arguments" should {
    "be searched in the order given, also when there are more than four" in {
      FileUtil.usingTemporaryDirectory("includePathOrderTests") { dir =>
        // Header `hi.h` is in directories i and i + 1. Only directory i's copy declares `fi` to return int.
        val directories = (1 to 8).map(i => dir / s"inc$i")
        directories.foreach(Files.createDirectories(_))
        (1 to 7).foreach { i =>
          Files.writeString(directories(i - 1) / s"h$i.h", s"int f$i(void);\n")
          Files.writeString(directories(i) / s"h$i.h", s"char f$i(void);\n")
        }
        val arguments = "." +: directories.flatMap(directory => Seq("--include", directory.toString))
        val config    = X2Cpg.parseCommandLine(arguments.toArray, Frontend.cmdLineParser, Config()).get
        val includes  = (1 to 7).map(i => s"#include <h$i.h>\n").mkString
        val calls     = (1 to 7).map(i => s"f$i()").mkString(" + ")
        val cpg       = code(s"${includes}int main(void) { return $calls; }\n", "main.c").withConfig(config)
        val functions = (1 to 7).map(i => s"f$i")
        cpg.call.nameExact(functions*).map(call => s"${call.name}:${call.typeFullName}").l.sorted shouldBe
          functions.map(name => s"$name:int").toList
      }
    }
  }

}
