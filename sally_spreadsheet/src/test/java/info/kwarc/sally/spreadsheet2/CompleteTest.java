package info.kwarc.sally.spreadsheet2;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.junit.runners.Suite.SuiteClasses;

@RunWith(Suite.class)
@SuiteClasses({ ManagerTest.class, OntologyRelationLinkTest.class,
		ValueInterpretationTest.class, VerificationDataExtractorTest.class, UtilTest.class })
public class CompleteTest {

}
