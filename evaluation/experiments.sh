echo ""
echo "1) Minimal examples"

echo ""
echo "  Monpoly 1"

cd examples/monpoly1
./run.sh
cd ../..

echo ""
echo "  Monpoly 2"
cd examples/monpoly2
./run.sh
cd ../..


echo ""
echo "  DejaVu 1"
cd examples/dejavu1
./run.sh
cd ../..

echo ""
echo "  DejaVu 2"
cd examples/dejavu2
./run.sh
cd ../..

echo ""
echo "  DejaVu 3"
cd examples/dejavu3
./run.sh
cd ../..

echo ""
echo "  Performance"
cd examples/performance
./run.sh
cd ../..

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
