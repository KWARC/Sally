package info.kwarc.sally.model.document.spreadsheet;

import java.util.List;

public class Legend extends AbstractStructure {
	AbstractSsElement header;
	List<AbstractSsElement> items;
	
	public Legend(int id, AbstractSsElement header, List<AbstractSsElement> items) {
		super(id);
		this.header = header;
		this.items = items;
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((header == null) ? 0 : header.hashCode());
		result = prime * result + ((items == null) ? 0 : items.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		Legend other = (Legend) obj;
		if (header == null) {
			if (other.header != null)
				return false;
		} else if (!header.equals(other.header))
			return false;
		if (items == null) {
			if (other.items != null)
				return false;
		} else if (!items.equals(other.items))
			return false;
		return true;
	}

	public AbstractSsElement getHeader() {
		return header;
	}

	public void setHeader(AbstractSsElement header) {
		this.header = header;
	}

	public List<AbstractSsElement> getItems() {
		return items;
	}
	
	public int getItemSize() {
		return items.size();
	}

	public void setItems(List<AbstractSsElement> items) {
		this.items = items;
	}
	
	public void removeItem(AbstractSsElement item) {
		items.remove(item);
	}
	
	public void addItem(AbstractSsElement item) {
		items.add(item);
	}
	
	public boolean contains(AbstractSsElement e) {
		return (items.contains(e) || ((header != null) && header.equals(e)));
	}
	
	public sally.LegendMsg getProtoBufRepresentation() {
		sally.LegendMsg.Builder msgBuilder = sally.LegendMsg.newBuilder();
		msgBuilder.setId(getId());
		if (header != null)
			msgBuilder.setHeader(header.getId());
		for (AbstractSsElement item : items)
			msgBuilder.addItems(item.getId());
		
		return msgBuilder.build();
	}

}
