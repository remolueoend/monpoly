echo ""
echo "1) Minimal examples"

echo ""
echo "  Monpoly 1 (paper 1)"

cd examples/examples-paper1/monpoly1
./run.sh
cd ../../..

echo ""
echo "  Monpoly 2 (paper 1)"
cd examples/examples-paper1/monpoly2
./run.sh
cd ../../..

echo ""
echo "  Monpoly 1 (paper 2)"
cd examples/examples-paper2/monpoly1
./run.sh
cd ../../..

echo ""
echo "  Monpoly 2 (paper 2)"
cd examples/examples-paper2/monpoly2
./run.sh
cd ../../..

echo ""
echo "  Monpoly 3 (paper 2)"
cd examples/examples-paper2/monpoly3
./run.sh
cd ../../..

echo ""
echo "  Monpoly 4 (paper 2)"
cd examples/examples-paper2/monpoly4
./run.sh
cd ../../..

echo ""
echo "  Monpoly 5 (paper 2)"
cd examples/examples-paper2/monpoly5
./run.sh
cd ../../..

echo ""
echo "  Monpoly 6 (paper 2)"
cd examples/examples-paper2/monpoly6
./run.sh
cd ../../..

echo ""
echo "  Hydra 1 (paper 2)"
cd examples/examples-paper2/hydra1
./run.sh
cd ../../..

echo ""
echo "  DejaVu 1"
cd examples/examples-paper1/dejavu1
./run.sh
cd ../../..

echo ""
echo "  DejaVu 2"
cd examples/examples-paper1/dejavu2
./run.sh
cd ../../..

echo ""
echo "  DejaVu 3"
cd examples/examples-paper1/dejavu3
./run.sh
cd ../../..

echo ""
echo "  Performance"
cd examples/examples-paper1/performance
./run.sh
cd ../../..

echo ""
echo "II) Differential testing experiments"

cd exp1
./experiments.sh
cd ..

cd exp2
./experiments.sh
cd ..

cd exp3
./experiments.sh
cd ..

cd exp4
./experiments.sh
cd ..

cd exp5
./experiments.sh
cd ..

cd exp6
./experiments.sh
cd ..
