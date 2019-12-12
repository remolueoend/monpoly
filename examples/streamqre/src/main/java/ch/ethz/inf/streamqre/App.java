package ch.ethz.inf.streamqre;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;
import java.util.Random;
import java.util.function.Predicate;

import StreamQRE.Eval;
import StreamQRE.QRe;
import StreamQRE.QReAtomic;
import StreamQRE.QReCombine;
import StreamQRE.QReIter;
import ex_patient.DItemMany;
import ex_patient.DItemOne;
import ex_patient.StreamMany;
import ex_patient.StreamOne;

/**
 * Hello world!
 *
 */
public class App 
{
	static private int epMin = 1;
	static private int epMax = 10;
	static private int mMin  = 1;
	static private int mMax  = 100;
	static private int patientNo  = 5;
	static private int seed;
	static private int length = 2;
	static private boolean monpoly = false;
	static private boolean singlePatient = false;
	
    public static void main( String[] args )
    {
    		Random r = new Random(42);
    		seed = r.nextInt();
    		parseArgs(args);
    		
    		StreamAdapter generator = singlePatient ? 
    				new StreamAdapter(epMin, epMax, mMin, mMax, seed):
    				new StreamAdapter(patientNo, epMin, epMax, mMin, mMax, seed);
    		
    		int s=0;
    		while(s!=length) {
    			DItemAdapter item = generator.next();
    			item = monpoly ? DItemAdapterMonpoly.of(item) : item;
    			if(item.isD()) {
    				s++;
    			}
    			System.out.println(item.toString());			
    		}
    		 
    	
    }
    private static void check(int value, Predicate<Integer> c, String msg) {
		if (!c.test(value)) {
			System.err.println(msg);
			System.exit(0);
		}
	}
	private static int parseArg(String argname, String argval) {
		try {
			return Integer.parseInt(argval);
		} catch (NumberFormatException e) {
			System.err.println("Parameter " + argname + " is not a valid integer");
			System.exit(0);
		}
		return 0;
	}


	private static void parseArgs(String[] args) {
		for(int i=0; i<args.length; i++) {
			try {
				switch (args[i]) {
					case "--emin":
					case "-emin":
						epMin = parseArg(args[i], args[i+1]);
						check(epMin, x->(x>=0),"Parameter " + args[i] + " cannot be negative");
						i++;
						break;
					case "--emax":
					case "-emax":
						epMax = parseArg(args[i], args[i+1]);
						check(epMax, x->(x>=0),"Parameter " + args[i] + " cannot be negative");
						i++;
						break;
					case "--mmin":
					case "-mmin":
						mMin = parseArg(args[i], args[i+1]);
						check(mMin, x->(x>=0),"Parameter " + args[i] + " cannot be negative");
						i++;
						break;
					case "--mmax":
					case "-mmax":
						mMax = parseArg(args[i], args[i+1]);
						check(mMax, x->(x>=0),"Parameter " + args[i] + " cannot be negative");
						i++;
						break;
					case "--seed":
					case "-seed":
						seed = parseArg(args[i], args[i+1]);
						i++;
						break;
					case "--monpoly":
					case "-monpoly":
					case "--m":
					case "-m":
						monpoly = true;
						break;
					case "--p":
					case "-p":
						patientNo = parseArg(args[i], args[i+1]);
						if(patientNo==1) singlePatient = true;
						check(patientNo, x->(x>0),"Parameter " + args[i] + " must be positive");
						i++;
						break;
					case "--length":
					case "-length":
						length = parseArg(args[i], args[i+1]);
						i++;
						break;
					case "--help":
					case "-help":
					case "--h":
					case "-h":
						printHelp();
						System.exit(1);
						break;
					default:
						System.err.println("Invalid parameter: " + args[i]);
						System.exit(0);
						break;
					}
			} catch (ArrayIndexOutOfBoundsException e) {
				System.err.println("Invalid number of parameters. Missing " + args[i]);
				System.exit(0);
			}
		}
		check(epMax-epMin, x->(x>0),"Parameter -emax must be greater than -emin");
		check(mMax-mMin, x->(x>0),"Parameter -mmax must be greater than -mmin");	
	}

	
	private static void printHelp() {
		System.out.println("Stream generator for the patient-episode-day QRE example");
		System.out.println("");
		System.out.println("Usage: java -jar <jarfile> [options]");
		System.out.println("");
		System.out.println("Options: \n\n" +
						   "   -emin N      Minimum episode number \n" +
						   "   -emax N      Maximum episode number \n" +
						   "   -mmin N      Minimum measurement value \n" +
						   "   -mmax N      Maxumum measurement value \n" +
						   "   -seed N      Random seed \n" +
						   "   -m -monpoly  Print in Monpoly format \n" +
						   "   -length N    Number of days (0 or negative for an infinite stream)\n" +
						   "   -help        Prints this help message" +
						   "\n");
		
	}
	static class StreamAdapter implements Iterator<DItemAdapter>{
		private StreamOne o = null;
		private StreamMany m = null;
		public StreamAdapter(int epMin, int epMax, int mMin, int mMax, long seed) {
			o = new StreamOne(epMin, epMax, mMin, mMax, seed);			
		}
		public StreamAdapter(int K, int epMin, int epMax, int mMin, int mMax, long seed) {
			m = new StreamMany(K, epMin, epMax, mMin, mMax, seed);
		}
		@Override
		public boolean hasNext() {
			if(o!=null) {
				return o.hasNext();
			} else {
				return m.hasNext();
			}
		}
		@Override
		public DItemAdapter next() {
			if(o!=null) {
				return new DItemAdapter(o.next());
			} else {
				return new DItemAdapter(m.next());
			}
		}
		
	}
	
	static class DItemAdapter{
		public enum KIND{ B, M, E, D }
		private KIND to(ex_patient.DItemMany.KIND k) {
			switch (k) {
				case B:  return KIND.B;
				case M:  return KIND.M;
				case E:  return KIND.E;
				default: return KIND.D;
			}
		}
		
		private KIND to(ex_patient.DItemOne.KIND k) {
			switch (k) {
				case B:  return KIND.B;
				case M:  return KIND.M;
				case E:  return KIND.E;
				default: return KIND.D;
			}
		}

		DItemOne one = null;
		DItemMany many = null;
		
		public DItemAdapter(DItemOne o) {
			assert(o!=null);
			one=o;
		}
		public DItemAdapter(DItemMany m) {
			assert(m!=null);
			many=m;
		}
		
		/**
		 * 
		 */
		private static final long serialVersionUID = 1L;
		public boolean isD() {
			if(one!=null) {
				return one.isD();
			} else {
				return many.isD();
			}
		}
		
		@Override
		public String toString() {
			if(one!=null) {
				return one.toString();
			} else {
				return many.toString();
			}
		}
		
		public KIND getKind() {
			if(one!=null) {
				return to(one.getKind());
			} else {
				return to(many.getKind());
			}
		}
		
		
	}
	static class DItemAdapterMonpoly extends DItemAdapter{
		public DItemAdapterMonpoly(DItemOne o) {
			super(o);
		}
		public DItemAdapterMonpoly(DItemMany m) {
			super(m);
		}
		
		public static DItemAdapterMonpoly of(DItemAdapter item) {
			return item.one!=null ? 
				new DItemAdapterMonpoly(item.one):
				new DItemAdapterMonpoly(item.many);
		}

		@Override
		public String toString() {
			return "@0 " + super.toString() + 
					(one!=null ?
					(getKind()==KIND.D || getKind()==KIND.B || getKind()==KIND.E ? "()" : ""):
					(getKind()==KIND.D ? "()" : ""));
						
		}
	}
	
	private static void trivialExample() {
		// Processes a single data item.
		QRe<Double, Double> item = 
				new QReAtomic<Double, Double>(x -> true, x -> x);
		
		// Computes the running sum.
		QRe<Double, Double> sum = 
				new QReIter<Double, Double, Double, Double>(item, 0.0, (x,y) -> x+y, x->x);
		
		// Computes the running count.
		QRe<Double, Long> count = 
				new QReIter<Double, Double, Long, Long>(item, 0L, (x,y) -> x+1,x->x);

		// Computes the running average.
		QRe<Double, Double> avg = 
				new QReCombine<Double, Double, Long, Double>(sum, count, (x,y) -> x/y);
		
		Eval<Double, Double> eval = avg.getEval().start();
		List<Double> input = new ArrayList<Double>(Arrays.asList(1.0,2.0,3.0,5.0,8.0,13.0,21.0));
		
		for (Double double1 : input) {
			eval=eval.next(double1);
		}
		System.out.println("Done! Result: " + (Double)eval.getOutput());
		
	}
}
