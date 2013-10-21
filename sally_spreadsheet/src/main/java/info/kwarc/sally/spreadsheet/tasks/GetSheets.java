package info.kwarc.sally.spreadsheet.tasks;

import info.kwarc.sally.core.DocumentInformation;
import info.kwarc.sally.core.DocumentManager;
import info.kwarc.sally.core.comm.CallbackManager;
import info.kwarc.sally.core.interfaces.SallyTask;
import info.kwarc.sally.core.net.IMessageCallback;
import info.kwarc.sally.spreadsheet.SpreadsheetDocument;
import info.kwarc.sissi.bpm.tasks.HandlerUtils;

import org.drools.process.instance.WorkItemHandler;
import org.drools.runtime.process.WorkItem;
import org.drools.runtime.process.WorkItemManager;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import sally.SpreadsheetDocMeta;

import com.google.inject.Inject;
import com.google.protobuf.AbstractMessage;

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
		final sally.GetMeta  gm = HandlerUtils.getFirstTypedParameter(workItem.getParameters(), sally.GetMeta.class);
		log.info("Create Blocks "+gm);
		try {
			if (gm == null)
				throw new Exception("No Get Meta object");
			DocumentInformation docInfo = docManager.getDocumentInformation(workItem);
			Object docModel = docInfo.getDocumentModel();
			if (!(docModel instanceof SpreadsheetDocument))
				throw new Exception("No document model");
			SpreadsheetDocument spdoc = (SpreadsheetDocument) docModel;

			docInfo.getNetworkSender().sendMessage("/service/get/meta", gm, new IMessageCallback() {
				
				@Override
				public void onMessage(AbstractMessage msg) {
					SpreadsheetDocMeta result = (SpreadsheetDocMeta) msg;
					
					if (gm.hasCallbackToken()) {
						callbacks.getCallback(gm.getCallbackToken()).run(result);
					}
					
				}
			});
			
		} catch (Exception e) {
			e.printStackTrace();
			log.error(e.getMessage());
		} finally {
			manager.completeWorkItem(workItem.getId(), workItem.getResults());
		}

	}


}
