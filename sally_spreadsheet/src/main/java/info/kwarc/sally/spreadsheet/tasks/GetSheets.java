package info.kwarc.sally.spreadsheet.tasks;

import info.kwarc.sally.core.doc.DocumentInformation;
import info.kwarc.sally.core.doc.DocumentManager;
import info.kwarc.sally.core.interaction.CallbackManager;
import info.kwarc.sally.core.workflow.SallyTask;
import info.kwarc.sally.core.workflow.WorkItem;
import info.kwarc.sally.core.workflow.WorkItemHandler;
import info.kwarc.sally.core.workflow.WorkItemManager;
import info.kwarc.sally.sharejs.models.SpreadsheetModel;
import info.kwarc.sally.spreadsheet.SpreadsheetDocument;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import Sally.SpreadsheetDocMeta;

import com.google.inject.Inject;

@SallyTask(action="GetSheets")
public class GetSheets implements WorkItemHandler  {
	Logger log;
	DocumentManager docManager;
	CallbackManager callbacks;

	@Inject
	public GetSheets(DocumentManager manager, CallbackManager callbacks) {
		this.docManager = manager;
		this.callbacks = callbacks;
		log = LoggerFactory.getLogger(getClass());
	}

	@Override
	public void abortWorkItem(WorkItem workItem, WorkItemManager manager) {
	}

	@Override
	public void executeWorkItem(WorkItem workItem, WorkItemManager manager) {
		final Sally.GetSheets gm = workItem.getFirstTypedParameter(Sally.GetSheets.class);
		log.info("Create Blocks "+gm);
		try {
			if (gm == null)
				throw new Exception("No Get Meta object");
			DocumentInformation docInfo = docManager.getDocumentInformation(workItem);
			Object docModel = docInfo.getDocumentModel();
			if (!(docModel instanceof SpreadsheetDocument))
				throw new Exception("No document model");
			SpreadsheetDocument spdoc = (SpreadsheetDocument) docModel;
			SpreadsheetModel spreadsheetModel = spdoc.getConcreteSpreadsheetModel();

			SpreadsheetDocMeta.Builder result = SpreadsheetDocMeta .newBuilder().setFileName(spdoc.getFilePath());
			for (String keys : spreadsheetModel.getSheets().keySet()) {
				result.addSheets(keys);
			}
						
			if (gm.hasCallbackToken()) {
				callbacks.getCallback(gm.getCallbackToken()).onMessage(result.build());
			}
			
		} catch (Exception e) {
			e.printStackTrace();
			log.error(e.getMessage());
		} finally {
			manager.completeWorkItem(workItem);
		}

	}


}
