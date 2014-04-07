package info.kwarc.sissi.model.document.cad.tasks;

import info.kwarc.sally.core.theo.Coordinates;
import info.kwarc.sally.core.theo.ScreenCoordinatesProvider;
import info.kwarc.sally.core.workflow.SallyTask;
import info.kwarc.sally.core.workflow.WorkItem;
import info.kwarc.sally.core.workflow.WorkItemHandler;
import info.kwarc.sally.core.workflow.WorkItemManager;

import java.util.PriorityQueue;

import Sally.CADAlexClick;
import Sally.ScreenCoordinates;

import com.google.inject.Inject;

@SallyTask(action="CADSelectionForwarder")
public class CADSelectionForward implements WorkItemHandler {

	class Workflow implements Comparable<Workflow>{
		int weight;

		@Override
		public int compareTo(Workflow o) {
			if (weight < o.weight)
				return -1;
			if (weight > o.weight)
				return 1;
			return 0;
		}
		
	}
	
	ScreenCoordinatesProvider coordProvider;
	PriorityQueue<Workflow> services;
	
	@Inject
	public CADSelectionForward(ScreenCoordinatesProvider coordProvider) {
		this.coordProvider = coordProvider;
	}
	
	@Override
	public void executeWorkItem(WorkItem workItem, WorkItemManager manager) {
		try {
			CADAlexClick click = workItem.getFirstTypedParameter(CADAlexClick.class);
			ScreenCoordinates pos = click.getPosition();
			coordProvider.setRecommendedCoordinates(new Coordinates(pos.getX(), pos.getY()));
		} catch (Exception e) {
			
		} finally {
			manager.completeWorkItem(workItem);
		}
	}

	@Override
	public void abortWorkItem(WorkItem workItem, WorkItemManager manager) {
		
	}

}
