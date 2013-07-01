package hk.ust.cse.Star.CrashModel;

import hk.ust.cse.Prevision.PathCondition.BinaryConditionTerm;
import hk.ust.cse.Prevision.PathCondition.BinaryConditionTerm.Comparator;
import hk.ust.cse.Prevision.PathCondition.Condition;
import hk.ust.cse.Prevision.PathCondition.ConditionTerm;
import hk.ust.cse.Prevision.PathCondition.Formula;
import hk.ust.cse.Prevision.Solver.SMTChecker.SatModelProcessor;
import hk.ust.cse.Prevision.VirtualMachine.Instance;

import java.util.ArrayList;
import java.util.Enumeration;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.List;

public class UseRangeProcessor extends SatModelProcessor {

  @Override
  public List<ConditionTerm> process(List<ConditionTerm> satModel, Formula formula) {
    // find all numerical instances in sat model
    List<String> matchStrings     = new ArrayList<String>();
    List<Instance> numInstances   = new ArrayList<Instance>();
    List<ConditionTerm> numModels = new ArrayList<ConditionTerm>();
    for (ConditionTerm modelTerm : satModel) {
      if (modelTerm instanceof BinaryConditionTerm) {
        Instance instance1 = ((BinaryConditionTerm) modelTerm).getInstance1();
        if (instance1.getLastReference() != null && instance1.getLastRefType().equals("I")) {
          numInstances.add(instance1);
          numModels.add(modelTerm);
          
          String matchString = instance1.toString();
          Instance topInstance = instance1.getToppestInstance();
          if (topInstance != instance1 && topInstance.isRelationRead()) {
            // read_@@array_117097066461950.realThing.project.references.count
            matchString = matchString.substring(topInstance.toString().length());
          }
          matchStrings.add(matchString);
        }
      }
    }
    
    // match numerical instances with the conditions in formula
    Hashtable<Instance, List<BinaryConditionTerm>> numericalTerms = new Hashtable<Instance, List<BinaryConditionTerm>>();
    for (int i = 0, size = formula.getConditionList().size(); i < size && numInstances.size() > 0; i++) {
      Condition condition = formula.getConditionList().get(i);
      
      boolean addedCondition = false; 
      BinaryConditionTerm binaryTerm = condition.getOnlyBinaryTerm();
      if (binaryTerm != null) {
        boolean toSwitch   = binaryTerm.getInstance1().isConstant();
        Instance instance1 = toSwitch ? binaryTerm.getInstance2() : binaryTerm.getInstance1();
        Instance instance2 = toSwitch ? binaryTerm.getInstance1() : binaryTerm.getInstance2();
        
        // e.g. v1.elementData.length >= 0
        if (!instance1.isConstant() && instance2.isConstant()) {
          String instance1Str = instance1.toString();
          for (int j = 0; j < numInstances.size(); j++) {
            if (matchedInstance(instance1, matchStrings.get(j))) {
              List<BinaryConditionTerm> terms = numericalTerms.get(numInstances.get(j));
              if (terms == null) {
                terms = new ArrayList<BinaryConditionTerm>();
                terms.add(toSwitch ? binaryTerm.flip() : binaryTerm);
                numericalTerms.put(numInstances.get(j), terms);
                addedCondition = true;
              }
              else {
                if (terms.get(0).getInstance1().toString().equals(instance1Str)) {
                  terms.add(toSwitch ? binaryTerm.flip() : binaryTerm);
                  addedCondition = true;
                }
              }
            }
          }
        }
      }
      
      // remove all numerical instances appearing in a not added condition
      if (!addedCondition) {
        HashSet<Instance> instances = condition.getRelatedInstances(formula.getRelationMap(), false, true, true, false);
        for (Instance instance : instances) {
          for (int j = 0; j < numInstances.size(); j++) {
            if (matchedInstance(instance, matchStrings.get(j))) {
              numericalTerms.remove(numInstances.get(j));
              numInstances.remove(j);
              matchStrings.remove(j);
              numModels.remove(j);
              break;
            }
          }
        }
      }
    }
    
    // retain only the necessary conditions
    Enumeration<Instance> keys = numericalTerms.keys();
    while (keys.hasMoreElements()) {
      Instance numInstance = (Instance) keys.nextElement();
      
      boolean hasEqual = false;
      long greaterThan = Long.MIN_VALUE;
      long smallerThan = Long.MAX_VALUE;
      BinaryConditionTerm greater = null;
      BinaryConditionTerm smaller = null;
      List<BinaryConditionTerm> other = new ArrayList<BinaryConditionTerm>();
      List<BinaryConditionTerm> terms = numericalTerms.get(numInstance);
      for (BinaryConditionTerm binaryTerm : terms) {
        int num = Integer.parseInt(binaryTerm.getInstance2().getValueWithoutPrefix());
        num = binaryTerm.getComparator() == Comparator.OP_GREATER_EQUAL ? num - 1 : 
              binaryTerm.getComparator() == Comparator.OP_SMALLER_EQUAL ? num + 1 : num;
        
        switch (binaryTerm.getComparator()) {
        case OP_EQUAL:
          hasEqual = true;
          break;
        case OP_GREATER:
        case OP_GREATER_EQUAL:
          if (num > greaterThan) {
            greater = binaryTerm;
            greaterThan = num;
          }
          break;
        case OP_INEQUAL:
          other.add(binaryTerm);
          break;
        case OP_SMALLER:
        case OP_SMALLER_EQUAL:
          if (num < smallerThan) {
            smaller = binaryTerm;
            smallerThan = num;
          }
          break;
        }
      }
      if (!hasEqual) {
        terms.clear();
        if (greater != null) {
          terms.add(greater);
        }
        if (smaller != null) {
          terms.add(smaller);
        }
        terms.addAll(other);
      }
      else {
        numericalTerms.remove(numInstance);
      }
    }
    
    // create the new satModel
    List<ConditionTerm> newSatModel = new ArrayList<ConditionTerm>(satModel);
    keys = numericalTerms.keys();
    while (keys.hasMoreElements()) {
      Instance numInstance = (Instance) keys.nextElement();
      
      // remove the original model term first
      ConditionTerm origTerm = numModels.get(numInstances.indexOf(numInstance));
      int index = newSatModel.indexOf(origTerm);
      newSatModel.remove(index);
      
      // add the new condition terms
      newSatModel.addAll(index, numericalTerms.get(numInstance));
    }
    
    return newSatModel;
  }

  private boolean matchedInstance(Instance instance, String matchString) {
    String instanceStr = instance.toString();
    Instance topInstance = instance.getToppestInstance();
    if (topInstance != instance && topInstance.isRelationRead()) {
      instanceStr = instanceStr.substring(topInstance.toString().length());
    }
    return instanceStr.equals(matchString);
  }
}
