package info.kwarc.sally.core;

import info.kwarc.sally.core.workflow.ISallyWorkflowManager;

import java.util.HashMap;

import org.drools.runtime.process.WorkItem;

import com.google.inject.Inject;
import com.google.inject.Singleton;

/**
 * This class defines a Singleton object that stores information about the documents 
 * managed by Sally such as
 *    - Process ID of the document workflow
 * @author Constantin Jucovschi
 *
 */
@Singleton
public class DocumentManager {

	HashMap<String, DocumentInformation> docProcessMap;
	HashMap<Long, DocumentInformation> processDocMap;
	ISallyWorkflowManager workflowManager;

	@Inject
	public DocumentManager(ISallyWorkflowManager workflowManager) {
		docProcessMap = new HashMap<String, DocumentInformation> ();
		this.workflowManager = workflowManager;
		processDocMap = new HashMap<Long, DocumentInformation>();
	}
	
	// Gets document information associated with a workflow task
	public DocumentInformation getDocumentInformation(WorkItem wi) {
		Long pid = wi.getProcessInstanceId();
		while (pid != null) {
			if (processDocMap.containsKey(pid)) {
				return processDocMap.get(pid);
			}
			pid = workflowManager.getWorkflowParent(pid);
		}
		return null;
	}

	public void addDocument(DocumentInformation docInfo) {
		processDocMap.put(docInfo.getDocumentWorkflowID(), docInfo);
		docProcessMap.put(docInfo.getFileName(), docInfo);
	}

	public DocumentInformation getDocumentInformation(String fileName) {
		return docProcessMap.get(fileName);
	}
}
