package info.kwarc.sally.spreadsheet.tasks;

import info.kwarc.sally.core.DocumentInformation;
import info.kwarc.sally.core.DocumentManager;
import info.kwarc.sally.core.comm.CallbackManager;
import info.kwarc.sally.core.interfaces.SallyTask;
import info.kwarc.sally.spreadsheet.SpreadsheetDocument;
import info.kwarc.sally.spreadsheet3.Util;
import info.kwarc.sally.spreadsheet3.model.Block;
import info.kwarc.sally.spreadsheet3.model.Relation;
import info.kwarc.sally.spreadsheet3.model.Relation.RelationType;
import info.kwarc.sissi.bpm.tasks.HandlerUtils;

import org.drools.process.instance.WorkItemHandler;
import org.drools.runtime.process.WorkItem;
import org.drools.runtime.process.WorkItemManager;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import sally.BlockInfo;
import sally.BlockList;

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
		sally.GetBlocks getBlocks = HandlerUtils.getFirstTypedParameter(workItem.getParameters(), sally.GetBlocks.class);
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
				callbacks.getCallback(getBlocks.getCallbackToken()).run(result.build());
			}
			
		} catch (Exception e) {
			e.printStackTrace();
			log.error(e.getMessage());
		} finally {
			manager.completeWorkItem(workItem.getId(), workItem.getResults());
		}

	}


}
