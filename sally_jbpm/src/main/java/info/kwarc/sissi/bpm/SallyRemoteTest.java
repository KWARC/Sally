package info.kwarc.sissi.bpm;

import org.drools.KnowledgeBase;
import org.drools.builder.KnowledgeBuilder;
import org.drools.builder.KnowledgeBuilderFactory;
import org.drools.builder.ResourceType;
import org.drools.io.ResourceFactory;
import org.drools.io.impl.UrlResource;

public class SallyRemoteTest {
//	static String sallyPackage = "http://localhost:8080/drools-guvnor/org.drools.guvnor.Guvnor/package/mortgages/TEST.drl";
	static String sallyPackage = "http://localhost:8080/drools-guvnor/org.drools.guvnor.Guvnor/package/Sally/LATEST";

	public static final void main(String[] args) throws Exception {
		
		UrlResource standardUrlResource = (UrlResource)ResourceFactory.newUrlResource(sallyPackage);
		standardUrlResource.setBasicAuthentication("enabled");
		standardUrlResource.setUsername("admin");
		standardUrlResource.setPassword("admin");

		KnowledgeBuilder kbuilder = KnowledgeBuilderFactory.newKnowledgeBuilder();
		kbuilder.add(standardUrlResource, ResourceType.PKG);
		KnowledgeBase kb = kbuilder.newKnowledgeBase();
		kb.newStatefulKnowledgeSession().startProcess("bpmn.connect");
	}
}
