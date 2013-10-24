package info.kwarc.sally.spreadsheet.tasks;

import java.util.ArrayList;
import java.util.List;

import info.kwarc.sally.core.DocumentInformation;
import info.kwarc.sally.core.DocumentManager;
import info.kwarc.sally.core.comm.CallbackManager;
import info.kwarc.sally.core.interfaces.SallyTask;
import info.kwarc.sally.spreadsheet.SpreadsheetDocument;
import info.kwarc.sally.spreadsheet3.Util;
import info.kwarc.sally.spreadsheet3.model.Block;
import info.kwarc.sally.spreadsheet3.model.CellDependencyDescription;
import info.kwarc.sally.spreadsheet3.model.RangeInformation;
import info.kwarc.sally.spreadsheet3.model.Relation;
import info.kwarc.sissi.bpm.tasks.HandlerUtils;

import org.drools.process.instance.WorkItemHandler;
import org.drools.runtime.process.WorkItem;
import org.drools.runtime.process.WorkItemManager;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import sally.BlockInfo;

import com.google.inject.Inject;

@SallyTask(action="CreateBlock")
public class CreateBlock implements WorkItemHandler  {
	Logger log;
	DocumentManager docManager;
	CallbackManager callbacks;

	@Inject
	public CreateBlock(DocumentManager manager, CallbackManager callbacks) {
		this.docManager = manager;
		this.callbacks = callbacks;
		log = LoggerFactory.getLogger(getClass());
	}

	@Override
	public void abortWorkItem(WorkItem workItem, WorkItemManager manager) {
	}

	@Override
	public void executeWorkItem(WorkItem workItem, WorkItemManager manager) {
		sally.CreateBlock cb = HandlerUtils.getFirstTypedParameter(workItem.getParameters(), sally.CreateBlock.class);
		log.info("Create Blocks "+cb);
		try {
			if (cb == null)
				throw new Exception("No Create Block ");
			DocumentInformation docInfo = docManager.getDocumentInformation(workItem);
			Object docModel = docInfo.getDocumentModel();
			if (!(docModel instanceof SpreadsheetDocument))
				throw new Exception("No Create Block ");
			SpreadsheetDocument spdoc = (SpreadsheetDocument) docModel;
			BlockInfo bi = cb.getBlockInfo();
			String range = bi.getRange();
			RangeInformation rng = Util.convertRangeAddress(range);
			Block block = spdoc.createBlock(rng.getWorksheet(), rng.getStartRow(), rng.getStartCol(), rng.getEndRow(), rng.getEndCol());

			List<Block> blocksInput = new ArrayList<Block>();
			blocksInput.add(block);

			List<CellDependencyDescription> relationInputDesc = new ArrayList<CellDependencyDescription>();
			relationInputDesc.add(new CellDependencyDescription(0,rng.getEndRow()-rng.getStartRow(),0,rng.getEndCol()-rng.getStartCol(),"x,y"));
			Relation r = spdoc.getASMModel().createRelation(Relation.RelationType.LABELRELATION, blocksInput, relationInputDesc);
			r.setUri(bi.getMeaning());
			if (cb.hasCallbackToken()) {
				callbacks.getCallback(cb.getCallbackToken()).run(BlockInfo.newBuilder().setId(block.getId()).build());
			}
		} catch (Exception e) {
			e.printStackTrace();
			log.error(e.getMessage());
		} finally {
			manager.completeWorkItem(workItem.getId(), workItem.getResults());
		}

	}


}
