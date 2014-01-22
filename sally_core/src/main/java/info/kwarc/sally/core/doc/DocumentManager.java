package info.kwarc.sally.core.doc;

import info.kwarc.sally.core.workflow.ISallyWorkflowManager;

import java.util.HashMap;

import org.drools.runtime.process.WorkItem;

import com.google.inject.Inject;
import com.google.inject.Singleton;

/**
 * @author Constantin Jucovschi
 * This class defines a Singleton object that stores information about the documents 
 * managed by Sally. Detailed document information are stored in the DocumentInformation
 * object. The DocumentManager class soleley indexes them by filename (fileNameMap) and
 * by workflow id (workflowMap). 
 */
@Singleton
public class DocumentManager {

	HashMap<String, DocumentInformation> fileNameMap;
	HashMap<Long, DocumentInformation> workflowMap;
	
	ISallyWorkflowManager workflowManager;

	@Inject
	public DocumentManager(ISallyWorkflowManager workflowManager) {
		fileNameMap = new HashMap<String, DocumentInformation> ();
		this.workflowManager = workflowManager;
		workflowMap = new HashMap<Long, DocumentInformation>();
	}

	// Gets document information associated with a workflow task
	public DocumentInformation getDocumentInformation(Long pid) {
		while (pid != null) {
			if (workflowMap.containsKey(pid)) {
				return workflowMap.get(pid);
			}
			pid = workflowManager.getWorkflowParent(pid);
		}
		return null;
	}

	// Gets document information associated with a workflow task
	public DocumentInformation getDocumentInformation(WorkItem wi) {
		return getDocumentInformation(wi.getProcessInstanceId());
	}

	public void addDocument(DocumentInformation docInfo) {
		workflowMap.put(docInfo.getDocumentWorkflowID(), docInfo);
		fileNameMap.put(docInfo.getFileName(), docInfo);
	}

	public DocumentInformation getDocumentInformation(String fileName) {
		return fileNameMap.get(fileName);
	}
}
