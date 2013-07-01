package hk.ust.cse.Star.CrashModel;

import hk.ust.cse.Prevision.PathCondition.BinaryConditionTerm;
import hk.ust.cse.Prevision.PathCondition.Condition;
import hk.ust.cse.Prevision.PathCondition.ConditionTerm;
import hk.ust.cse.Prevision.PathCondition.Formula;
import hk.ust.cse.Prevision.PathCondition.TypeConditionTerm;
import hk.ust.cse.Prevision.PathCondition.TypeConditionTerm.Comparator;
import hk.ust.cse.Prevision.Solver.SMTChecker.SatModelProcessor;
import hk.ust.cse.Prevision.VirtualMachine.Instance;

import java.util.HashSet;
import java.util.List;

public class LessTypeRestrict extends SatModelProcessor {

  @Override
  public List<ConditionTerm> process(List<ConditionTerm> satModel, Formula formula) {
    // collect all instances which have type constraints on them
    HashSet<String> instancesWithTypeTerm = new HashSet<String>();
    for (Condition condition : formula.getConditionList()) {
      for (ConditionTerm term : condition.getConditionTerms()) {
        if (term instanceof TypeConditionTerm) {
          instancesWithTypeTerm.add(((TypeConditionTerm) term).getInstance1().toString());
        }
        else if (term instanceof BinaryConditionTerm) {
          Instance instance1 = ((BinaryConditionTerm) term).getInstance1();
          if (instance1.getLastReference() != null && instance1.getLastRefName().startsWith(("__instanceof__"))) {
            instancesWithTypeTerm.add(instance1.getLastReference().getDeclaringInstance().toString());
          }
        }
      }
    }
    
    for (int i = 0, size = satModel.size(); i < size; i++) {
      ConditionTerm modelTerm = satModel.get(i);
      if (modelTerm instanceof TypeConditionTerm) {
        Instance instance = ((TypeConditionTerm) modelTerm).getInstance1();
        String modelType  = ((TypeConditionTerm) modelTerm).getTypeString();
        
        String origType = instance.getType();
        origType = (origType == null && instance.getLastReference() != null) ? instance.getLastRefType() : origType;
        if (origType != null && !origType.equals(modelType)) { // used a more specific type in model, but it may not always be necessary
          if (!shouldUseModelType(instancesWithTypeTerm, instance)) {
            Comparator comp  = ((TypeConditionTerm) modelTerm).getComparator();
            satModel.set(i, new TypeConditionTerm(instance, comp, origType));
          }
        }
      }
    }
    
    return satModel;
  }
  
  // since the SMT solver may give some very specific type to the instance which does
  // not make any sense (just a specific model), we only use this type information 
  // when 1) there are explicit type constraints for this instance in validateFormula 
  private boolean shouldUseModelType(HashSet<String> instancesWithTypeTerm, Instance instance1) {
    
    boolean shouldUseModelType = false;
    if (instancesWithTypeTerm.contains(instance1.toString())) {
      shouldUseModelType = true; // 1) there are explicit type constraints for this instance in validateFormula 
    }
    return shouldUseModelType;
  }
}
