package info.kwarc.sally.spreadsheet3;

import info.kwarc.sally.spreadsheet3.logic.CDDBuilderTest;
import info.kwarc.sally.spreadsheet3.logic.RelationBuilderTest;
import info.kwarc.sally.spreadsheet3.logic.RelationInterpreterTest;
import info.kwarc.sally.spreadsheet3.model.ManagerTest;
import info.kwarc.sally.spreadsheet3.ontology.ValueInterpretationTest;
import info.kwarc.sally.spreadsheet3.verification.VerificationDataExtractorTest;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.junit.runners.Suite.SuiteClasses;

@RunWith(Suite.class)
@SuiteClasses({ RelationBuilderTest.class, RelationInterpreterTest.class, ManagerTest.class, 
		ValueInterpretationTest.class, VerificationDataExtractorTest.class, UtilTest.class, CDDBuilderTest.class })

public class CompleteTest {

}
