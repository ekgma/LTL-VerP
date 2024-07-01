#!/bin/bash

chmod +x solvers/aspicV3.4
chmod +x solvers/lsting
chmod +x solvers/mathsat
chmod +x solvers/z3


echo "------------------Building the existential artifact------------------"
cd src/existential
javac -cp . Main.java

cd ../..
jar cfm existential.jar src/existential/META-INF/MANIFEST.MF src/existential/*.class

echo "------------------Building the universal artifact------------------"
cd src/universal
javac -cp . Main.java

cd ../..
jar cfm universal.jar src/universal/META-INF/MANIFEST.MF src/universal/*.class
echo "------------------Artifact Build finished successfully------------------"
