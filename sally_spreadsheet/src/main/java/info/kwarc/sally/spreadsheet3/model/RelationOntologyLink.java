package info.kwarc.sally.spreadsheet3.model;

import java.util.ArrayList;
import java.util.List;

public class RelationOntologyLink {
	String uri;
	List<String> parameterLink;
	
	public RelationOntologyLink(String uri, List<String> parameterLink) {
		super();
		this.uri = uri;
		this.parameterLink = parameterLink;
	}
	
	public RelationOntologyLink(String uri, int size) {
		super();
		this.uri = uri;
		parameterLink = new ArrayList<String>();
		for (int i = 0 ; i < size; i++)
			parameterLink.add(new Integer(i).toString());
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result
				+ ((parameterLink == null) ? 0 : parameterLink.hashCode());
		result = prime * result + ((uri == null) ? 0 : uri.hashCode());
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
		RelationOntologyLink other = (RelationOntologyLink) obj;
		if (parameterLink == null) {
			if (other.parameterLink != null)
				return false;
		} else if (!parameterLink.equals(other.parameterLink))
			return false;
		if (uri == null) {
			if (other.uri != null)
				return false;
		} else if (!uri.equals(other.uri))
			return false;
		return true;
	}

	public boolean isBlockIndex(int index) {
		boolean isBlockIndex = false;
		try {
			int blockIndex = Integer.parseInt(parameterLink.get(index));
			if (blockIndex >= 0)
				isBlockIndex = true;
			
		} catch (NumberFormatException e) {}
		return isBlockIndex;
	}
	
	public int getBlockIndex(int index) {
		return Integer.parseInt(parameterLink.get(index));
	}
	
	public String getArgument_(int index) {
		return parameterLink.get(index);
	}
	
	public int size() {
		return parameterLink.size();
	}
	
	public String getUri() {
		return this.uri;
	}
	
	public void setUri(String uri) {
		this.uri = uri;
	}

}
