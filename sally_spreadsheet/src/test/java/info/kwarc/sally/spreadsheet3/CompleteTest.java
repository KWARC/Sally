package info.kwarc.sally.spreadsheet3;

import info.kwarc.sally.spreadsheet3.extraction.ExtractionInterfaceTest;
import info.kwarc.sally.spreadsheet3.logic.CDDBuilderTest;
import info.kwarc.sally.spreadsheet3.logic.RelationBuilderTest;
import info.kwarc.sally.spreadsheet3.logic.RelationInterpreterTest;
import info.kwarc.sally.spreadsheet3.model.ModelManagerTest;
import info.kwarc.sally.spreadsheet3.ontology.BuilderMathMLTest;
import info.kwarc.sally.spreadsheet3.ontology.SemanticModelManagerTest;
import info.kwarc.sally.spreadsheet3.ontology.ValueInterpretationTest;
import info.kwarc.sally.spreadsheet3.verification.VerificationDataExtractorTest;
import info.kwarc.sally.spreadsheet3.verification.VerificationSpecificationGeneratorTest;
import info.kwarc.sally.spreadsheet3.verification.VerifierTest;
import info.kwarc.sally.spreadsheet3.verification.Z3InterfaceTest;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.junit.runners.Suite.SuiteClasses;

@RunWith(Suite.class)
@SuiteClasses({ RelationBuilderTest.class, RelationInterpreterTest.class, ModelManagerTest.class, BuilderMathMLTest.class, ManagerTest.class,
		ValueInterpretationTest.class, VerificationDataExtractorTest.class, VerificationSpecificationGeneratorTest.class,
		UtilTest.class, CDDBuilderTest.class, Z3InterfaceTest.class, VerifierTest.class, ExtractionInterfaceTest.class,
		SemanticModelManagerTest.class})

public class CompleteTest {

}
