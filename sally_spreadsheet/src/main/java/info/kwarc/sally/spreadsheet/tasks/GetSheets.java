package info.kwarc.sally.spreadsheet.tasks;

import info.kwarc.sally.core.doc.DocumentInformation;
import info.kwarc.sally.core.doc.DocumentManager;
import info.kwarc.sally.core.interaction.CallbackManager;
import info.kwarc.sally.core.workflow.SallyTask;
import info.kwarc.sally.sharejs.models.SpreadsheetModel;
import info.kwarc.sally.spreadsheet.SpreadsheetDocument;
import info.kwarc.sissi.bpm.tasks.HandlerUtils;

import org.drools.process.instance.WorkItemHandler;
import org.drools.runtime.process.WorkItem;
import org.drools.runtime.process.WorkItemManager;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import sally.SpreadsheetDocMeta;

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
		final sally.GetSheets gm = HandlerUtils.getFirstTypedParameter(workItem.getParameters(), sally.GetSheets.class);
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
			manager.completeWorkItem(workItem.getId(), workItem.getResults());
		}

	}


}
