package hk.ust.cse.Star.CrashModel;

import hk.ust.cse.Prevision.InstructionHandlers.AbstractHandler;
import hk.ust.cse.Prevision.InstructionHandlers.CompleteBackwardHandler;
import hk.ust.cse.Prevision.Misc.CallStack;
import hk.ust.cse.Prevision.Misc.InvalidStackTraceException;
import hk.ust.cse.Prevision.PathCondition.Formula;
import hk.ust.cse.Prevision.Solver.SMTChecker;
import hk.ust.cse.Prevision.VirtualMachine.CallStackResult;
import hk.ust.cse.Prevision.VirtualMachine.ExecutionOptions;
import hk.ust.cse.Prevision.VirtualMachine.ExecutionOptions.EXCEPTION_TYPE;
import hk.ust.cse.Prevision.VirtualMachine.ExecutionResult;
import hk.ust.cse.Prevision.VirtualMachine.Executor.BackwardExecutor;
import hk.ust.cse.Wala.CallGraph.CallGraphBuilder;
import hk.ust.cse.Wala.Jar2IR;
import hk.ust.cse.util.Utils;
import hk.ust.cse.util.DbHelper.DbHelperSqlite;

import java.io.FileWriter;
import java.io.IOException;
import java.sql.Connection;
import java.sql.ResultSet;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import javax.naming.TimeLimitExceededException;

import com.ibm.wala.classLoader.IClass;
import com.ibm.wala.ssa.IR;

public class CrashModelGenerator {
  
  // can only be used to compute for one exception at a time as the target jarFile is different
  public CrashModelGenerator(String pseudoImplJarFile, String dbName, 
      String filterMethodFile, int accessibility, int exceptionID) throws Exception {
    
    m_pseudoImplJarFile = pseudoImplJarFile;
    m_filterMethodFile  = filterMethodFile;
    m_accessibility     = accessibility;
    m_exceptionID       = exceptionID;
    
    // crash model database name and table name
    m_dbName            = dbName;
    m_tableName         = "Model";
  }
  
  public void generateTable() {
    Connection conn = null;
    try {
      conn = DbHelperSqlite.openConnection(m_dbName);

      // always create a new table
      //createNewTable(conn);
      
      // load exception and initial executor
      initilize(conn);
      
      // generate data and populate them into table
      System.out.println("Populating model data into table...");
      
      // start time
      long start = System.currentTimeMillis();
      
      // keep track of the status
      FileWriter logger = new FileWriter("./Progress.txt");
      generateDataToDB(conn, logger);
      
      // end time
      long end = System.currentTimeMillis();
      String time = "Total elapsed: " + (end - start) + "ms";
      logger.write(time + "\n");
      logger.flush();
      logger.close();
      
      System.out.println(time);
      System.out.println("Population finished successfully!");
    } catch (Exception e) {
      e.printStackTrace();
    } finally {
      DbHelperSqlite.closeConnection(conn);
    }
  }

  // load the exception and initial the execution
  private void initilize(Connection conn) throws Exception {
    // load the exception to compute
    loadException(conn);
    String appJar = (String) m_exception[0];
    
    // initialize
    AbstractHandler instHandler = new CompleteBackwardHandler();
    instHandler.setMethodStepInFilters(m_filterMethodFile);
    SMTChecker smtChecker = new SMTChecker(SMTChecker.SOLVERS.Z3);
    smtChecker.addSatModelProcessor(new UseRangeProcessor());
    smtChecker.addSatModelProcessor(new LessTypeRestrict());
    
    m_executor = new BackwardExecutor(appJar, m_pseudoImplJarFile, instHandler, smtChecker);

    // load jar file, _removed.jar version is for faster call graph construction. Since it may 
    // be missing some classes (e.g. UnknownElement), we should use the full version in classloader
    appJar = appJar.endsWith("_removed.jar") ? appJar.substring(0, appJar.length() - 12) + ".jar" : appJar;
    Utils.loadJarFile(appJar);
  }
  
  private boolean generateDataToDB(Connection conn, FileWriter logger) throws Exception {
    List<Integer> noModelsList   = new ArrayList<Integer>();
    List<Integer> haveModelsList = new ArrayList<Integer>();
    
    // create call stack for each frame
    List<Object[]> frameCallStacks = genFrameCallStacks((CallStack) m_exception[9]);
    
    for (int i = 0, size = frameCallStacks.size(); i < size; i++) { //XXX
      CallStack cs = (CallStack) frameCallStacks.get(i)[0];
      int level    = (Integer) frameCallStacks.get(i)[1];
      
      // start time
      long start = System.currentTimeMillis();
      
      // log progress
      String progress = "Computing for level " + level + "...";
      logger.write(progress);
      logger.flush();
      System.out.println(progress);
    
      // model strings should be inserted to database in batch
      List<String> sqlTexts = new ArrayList<String>();
      
      System.out.println("Call Stack: " + cs.toString());
      CallStackResult callStackResult = computeCallStack(cs);
      
      // parse each sat-model
      List<String> modelStrings = new ArrayList<String>();

      List<Formula> satisfiables = callStackResult.getSatisfiables();
      for (int k = 0, size3 = satisfiables.size(); k < size3; k++) {
        Formula satisfiable = satisfiables.get(k);
        if (satisfiable != null) {
          // sat-model
          modelStrings.add(satisfiable.getLastSolverResult().convSatModelToString(satisfiable));

          // manually clear solver data to reduce memory usage
          satisfiable.clearSolverData();
        }
      }
      
      // delete redundant
      Utils.deleteRedundents(modelStrings);
      
      // store each sat-model into the Model table
      for (int k = 0, size3 = modelStrings.size(); k < size3; k++) {
        StringBuilder modelSqlText = new StringBuilder();
        modelSqlText.append("Insert Into ");
        modelSqlText.append(m_tableName);
        modelSqlText.append(" Values (Null, ");
        modelSqlText.append(m_exceptionID);;
        modelSqlText.append(", '");
        modelSqlText.append(cs.toString());
        modelSqlText.append("', '");
        modelSqlText.append(modelStrings.get(k));
        modelSqlText.append("')");   
        sqlTexts.add(modelSqlText.toString());
      }
      DbHelperSqlite.executeBatch(conn, sqlTexts.toArray(new String[0]));

      // end time
      long end = System.currentTimeMillis();
      logger.write(". Elapsed time: " + (end - start) + "ms\n");
      logger.flush();
      
      if (sqlTexts.size() == 0) {
        noModelsList.add(level);
        break; // no need to try the later frames anymore
      }
      else {
        haveModelsList.add(level);
      }
    }
    
    // output
    System.out.println("Number of frames cannot compute models: " + noModelsList.size()); 
    System.out.println("Number of frames with computed models: " + haveModelsList.size()); 
    for (int j = 0, size2 = haveModelsList.size(); j < size2; j++) {
      System.out.println(haveModelsList.get(j));
    }
    
    return true;
  }
  
  private List<Object[]> genFrameCallStacks(CallStack fullCallStack) {
    List<Object[]> frameCallStacks = new ArrayList<Object[]>();
    
    CallStack currentStack = fullCallStack;
    while (currentStack != null) {
      String methodName = currentStack.getCurMethodNameOrSign();
      int lineNo = currentStack.getCurLineNo();
      
      // add to all current stacks
      for (int i = 0, size = frameCallStacks.size(); i < size; i++) {
        ((CallStack) frameCallStacks.get(i)[0]).addStackTrace(methodName, lineNo);
      }
      
      IR ir = Jar2IR.getIR(m_executor.getWalaAnalyzer(), methodName, lineNo);
      if (ir != null && !ir.getMethod().isVolatile() /* Why are there 'volatile' methods? Anyway, skip them! */ && 
          !ir.getMethod().getName().toString().startsWith("access$")) {
         // if it is a public method of a public class, treat as an entry point
         if (m_accessibility == 0 && ir.getMethod().isPublic() && ir.getMethod().getDeclaringClass().isPublic()) {
           CallStack newEntry = new CallStack(true);
           newEntry.addStackTrace(methodName, lineNo);
           frameCallStacks.add(new Object[] {newEntry, currentStack.getDepth()});
         }
         // if it is a non-private method of a non-private class, treat as an entry point
         else if (m_accessibility == 1 && !ir.getMethod().isPrivate() && 
             !ir.getMethod().getDeclaringClass().isPrivate() /*&& !isAnonymousClass(ir.getMethod().getDeclaringClass())*/) {
           CallStack newEntry = new CallStack(true);
           newEntry.addStackTrace(methodName, lineNo);
           frameCallStacks.add(new Object[] {newEntry, currentStack.getDepth()});
         }
       }

      // next inner stack
      currentStack = currentStack.getInnerCallStack();
    }
    Collections.reverse(frameCallStacks);
    
    return frameCallStacks;
  }

  @SuppressWarnings("unused")
  private boolean isAnonymousClass(IClass cls) {
    String className = cls.getName().toString();
    int index = className.lastIndexOf('$');
    boolean isAnonymous = false;
    if (index >= 0) {
      try {
        Integer.parseInt(className.substring(index + 1));
        isAnonymous = true;
      } catch (Exception e) {}
    }
    return isAnonymous;
  }
  
  @SuppressWarnings("unused")
  private void createNewTable(Connection conn) throws Exception {
    // always drop old table first
    if (DbHelperSqlite.exist(conn, m_tableName)) {
      String sqlText = "Drop Table " + m_tableName;
      DbHelperSqlite.executeNonQuery(conn, sqlText);
    }
    
    // create new table
//    String sqlText = "Create Table " + m_tableName
//        + " (id Integer Not Null Primary Key AutoIncrement, ExceptionID Integer Not Null, " +
//            "CallStack Text Not Null, ConditionsString Text Not Null, PartialModelString Text Not Null, " +
//            "ModelString Text Not Null, ConditionsObjs Text Not Null, PartialModelObjs Text Not Null, " +
//            "ModelObjs Text Not Null, FOREIGN KEY(ExceptionID) REFERENCES Exception(id))";
    String sqlText = "Create Table " + m_tableName
        + " (id Integer Not Null Primary Key AutoIncrement, ExceptionID Integer Not Null, " +
            "CallStack Text Not Null, ModelString Text Not Null, FOREIGN KEY(ExceptionID) REFERENCES Exception(id))";
    DbHelperSqlite.executeNonQuery(conn, sqlText);
  }

  private Object[] loadException(Connection conn) throws Exception {
    m_exception = new Object[10];
    
    String sqlText = "Select * From Exception Where id = " + m_exceptionID;
    ResultSet rs = DbHelperSqlite.executeQuery(conn, sqlText);
    if (rs.next()) {
      // mandatory fields
      String jarFile          = rs.getString(4);
      String cgBuilder        = rs.getString(5);
      String excepType        = rs.getString(6);
      String outputDir        = rs.getString(7);
      
      // optional fields
      Integer maxDispTargets  = (Integer) rs.getObject(8);
      Integer maxRetrieve     = (Integer) rs.getObject(9);
      Integer maxSmtCheck     = (Integer) rs.getObject(10);
      Integer maxInvokeDepth  = (Integer) rs.getObject(11);
      Integer maxLoop         = (Integer) rs.getObject(12);

      String frames = rs.getString(13);
      CallStack callStack = null;
      if (frames != null && frames.length() > 0) {
        callStack = CallStack.fromString(frames);
      }
      
      m_exception[0] = jarFile;
      m_exception[1] = cgBuilder;
      m_exception[2] = excepType;
      m_exception[3] = outputDir;
      m_exception[4] = maxDispTargets;
      m_exception[5] = maxRetrieve;
      m_exception[6] = maxSmtCheck;
      m_exception[7] = maxInvokeDepth;
      m_exception[8] = maxLoop;
      m_exception[9] = callStack;
    }
    rs.close();

    return m_exception;
  }
  
  private CallStackResult computeCallStack(CallStack callStack) throws IOException {
    // compute many satModels for this call stack
    List<Formula> satisfiables = compute(callStack);
    ExecutionResult execResult = m_executor.getExecResult();
    
    // create output
    CallStackResult callStackResult = new CallStackResult(callStack, execResult);
    
    // parse result
    if (satisfiables.size() > 0) {
      for (Formula satisfiable : satisfiables) {
        // add one each time
        callStackResult.addSatisfiable(satisfiable);
      }
    }
    else {
      // assume solver cannot solve
      callStackResult.addSatisfiable(null); 
    }
    return callStackResult;
  }
  
  private List<Formula> compute(CallStack callStack) {
    List<Formula> satisfiables = new ArrayList<Formula>();
    try {
      // set symbolic execution properties
      int maxDispTargets  = (m_exception[4] != null) ? (Integer) m_exception[4] : 2;
      int maxRetrieve     = (m_exception[5] != null) ? (Integer) m_exception[5] : 10;
      int maxSmtCheck     = (m_exception[6] != null) ? (Integer) m_exception[6] : 1000;
      int maxInvokeDepth  = (m_exception[7] != null) ? (Integer) m_exception[7] : 10;
      int maxLoop         = (m_exception[8] != null) ? (Integer) m_exception[8] : 1;

      // prepare call graph builder
      CallGraphBuilder cgBuilder = CallGraphBuilder.ZeroOneCFA;
      if (m_exception[1] != null) {
        if (m_exception[1].equals("ZeroCFA")) {
          cgBuilder = CallGraphBuilder.ZeroCFA;
        }
        else if (m_exception[1].equals("ZeroOneCFA")) {
          cgBuilder = CallGraphBuilder.ZeroOneCFA;
        }
        else if (m_exception[1].equals("VanillaZeroOneCFA")) {
          cgBuilder = CallGraphBuilder.VanillaZeroOneCFA;
        }
        else if (m_exception[1].equals("ZeroContainerCFA")) {
          cgBuilder = CallGraphBuilder.ZeroContainerCFA;
        }
        else if (m_exception[1].equals("ZeroOneContainerCFA")) {
          cgBuilder = CallGraphBuilder.ZeroOneContainerCFA;
        }
        else if (m_exception[1].equals("VanillaZeroOneContainerCFA")) {
          cgBuilder = CallGraphBuilder.VanillaZeroOneContainerCFA;
        }
        else if (m_exception[1].equals("None")) {
          cgBuilder = null;
        }
      }
      
      // prepare exception type
      EXCEPTION_TYPE excepType = EXCEPTION_TYPE.CUSTOM;;
      if (m_exception[2].equals("NPE")) {
        excepType = EXCEPTION_TYPE.NPE;
      }
      else if (m_exception[2].equals("AIOBE")) {
        excepType = EXCEPTION_TYPE.AIOBE;
      }
      else {
        excepType = EXCEPTION_TYPE.CUSTOM;
      }
      
      // set options
      ExecutionOptions execOptions = new ExecutionOptions(callStack);
      execOptions.maxDispatchTargets     = maxDispTargets;
      execOptions.maxRetrieve            = maxRetrieve;
      execOptions.maxSmtCheck            = maxSmtCheck;
      execOptions.maxInvokeDepth         = maxInvokeDepth;
      execOptions.maxLoop                = maxLoop;
      execOptions.maxTimeAllow           = 100000;
      execOptions.clearSatNonSolverData  = false; /* we need the relationMap in abstractMemory */
      execOptions.addIRAsEntryPoint      = true;
      
      execOptions.exceptionType         = excepType;
      execOptions.callGraphBuilder      = cgBuilder;
//      execOptions.checkOnTheFly         = false;
//      execOptions.skipUselessBranches   = false;
//      execOptions.skipUselessMethods    = false;
//      execOptions.heuristicBacktrack    = false;
      
      m_executor.compute(execOptions, null);
    
    } catch (InvalidStackTraceException e) {
      System.err.println("Invalid Stack Trace!");
    } catch (TimeLimitExceededException e) {
      System.err.println("Time limit exceeded!");
    } catch (Exception e) {
      e.printStackTrace();
    } catch (OutOfMemoryError e) {
      System.err.println("Ran out of memory when computing for this call stack, skip!");
    }
    
    // get all satisfiables from executor
    if (m_executor.getExecResult() != null) {
      satisfiables.addAll(m_executor.getSatisfiables());
    }
    
    return satisfiables;
  }
  
  public static void main(String[] args) throws Exception {
    CrashModelGenerator modelGenerator = new CrashModelGenerator(args[0], 
                                                                 args[1], 
                                                                 args[2], 
                                                                 Integer.parseInt(args[3]), 
                                                                 Integer.parseInt(args[4]));
    modelGenerator.generateTable();
  }
  
  private Object[]         m_exception;
  private BackwardExecutor m_executor;

  private final int    m_exceptionID;
  private final int    m_accessibility; /* 0: only public; 1: public + default + protected */
  private final String m_dbName;
  private final String m_tableName;
  private final String m_pseudoImplJarFile;
  private final String m_filterMethodFile;
}
