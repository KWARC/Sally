package info.kwarc.sally.spreadsheet.tasks;

import info.kwarc.sally.core.doc.DocumentInformation;
import info.kwarc.sally.core.doc.DocumentManager;
import info.kwarc.sally.core.interaction.CallbackManager;
import info.kwarc.sally.core.workflow.SallyTask;
import info.kwarc.sally.core.workflow.WorkItem;
import info.kwarc.sally.core.workflow.WorkItemHandler;
import info.kwarc.sally.core.workflow.WorkItemManager;
import info.kwarc.sally.spreadsheet.SpreadsheetDocument;
import info.kwarc.sally.spreadsheet3.Util;
import info.kwarc.sally.spreadsheet3.model.Block;
import info.kwarc.sally.spreadsheet3.model.Relation;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import Sally.BlockInfo;
import Sally.BlockList;

import com.google.inject.Inject;

@SallyTask(action="GetBlocks")
public class GetBlocks implements WorkItemHandler  {
	Logger log;
	DocumentManager docManager;
	CallbackManager callbacks;
	
	@Inject
	public GetBlocks(DocumentManager manager, CallbackManager callbacks) {
		this.docManager = manager;
		this.callbacks = callbacks;
		log = LoggerFactory.getLogger(getClass());
	}

	@Override
	public void abortWorkItem(WorkItem workItem, WorkItemManager manager) {
	}

	@Override
	public void executeWorkItem(WorkItem workItem, WorkItemManager manager) {
		Sally.GetBlocks getBlocks = workItem.getFirstTypedParameter(Sally.GetBlocks.class);
		try {
			if (getBlocks == null)
				throw new Exception("No GetBlocks request ");

			DocumentInformation docInfo;
			if (getBlocks.hasFileName()) {
				docInfo = docManager.getDocumentInformation(getBlocks.getFileName());
			} else {				
				docInfo = docManager.getDocumentInformation(workItem);
			}
						
			Object docModel = docInfo.getDocumentModel();
			if (!(docModel instanceof SpreadsheetDocument))
				throw new Exception("No Create Block ");
			SpreadsheetDocument spdoc = (SpreadsheetDocument) docModel;

			BlockList.Builder result = BlockList.newBuilder();

			for (Relation r : spdoc.getASMModel().getAllRelations()) {
				//if (r.getRelationType() != RelationType.LABELRELATION) {
				//	continue;
				//}
				Block block = r.getBlocks().get(0);
				String blockRange = block.getWorksheet()+"!"
													+Util.convertIndex2RangeCharacter(block.getMinRow())
													+Integer.toString(block.getMinColumn()+1) + ":"
													+Util.convertIndex2RangeCharacter(block.getMaxRow())
													+Integer.toString(block.getMaxColumn()+1);
				
				result.addBlocks(BlockInfo.newBuilder()
						.setId(block.getId())
						.setMeaning(r.getUri())
						.setName("Name of "+block.getId())
						.setOrder(block.getId())
						.setRange(blockRange).build()						
						);
			}
			
			if (getBlocks.hasCallbackToken()) {
				callbacks.getCallback(getBlocks.getCallbackToken()).onMessage(result.build());
			}
			
		} catch (Exception e) {
			e.printStackTrace();
			log.error(e.getMessage());
		} finally {
			manager.completeWorkItem(workItem);
		}

	}


}
