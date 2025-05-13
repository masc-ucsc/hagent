brew install scala@2.12

curl -sSLf https://scala-cli.virtuslab.org/get | sh

scala-cli version

rm -rf .bsp .scala-build project target

scala-cli run 11_module_connection_buggy.scala \
  --scala 2.13.16 \
  --dependency "edu.berkeley.cs::chisel3:3.6.0"


sbt clean compile run
