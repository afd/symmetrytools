/* This file was generated by SableCC (http://www.sablecc.org/). */

package src.promela.node;

import src.promela.analysis.*;

@SuppressWarnings("nls")
public final class AOneActive extends PActive
{
    private TActivetok _activetok_;

    public AOneActive()
    {
        // Constructor
    }

    public AOneActive(
        @SuppressWarnings("hiding") TActivetok _activetok_)
    {
        // Constructor
        setActivetok(_activetok_);

    }

    @Override
    public Object clone()
    {
        return new AOneActive(
            cloneNode(this._activetok_));
    }

    public void apply(Switch sw)
    {
        ((Analysis) sw).caseAOneActive(this);
    }

    public TActivetok getActivetok()
    {
        return this._activetok_;
    }

    public void setActivetok(TActivetok node)
    {
        if(this._activetok_ != null)
        {
            this._activetok_.parent(null);
        }

        if(node != null)
        {
            if(node.parent() != null)
            {
                node.parent().removeChild(node);
            }

            node.parent(this);
        }

        this._activetok_ = node;
    }

    @Override
    public String toString()
    {
        return ""
            + toString(this._activetok_);
    }

    @Override
    void removeChild(@SuppressWarnings("unused") Node child)
    {
        // Remove child
        if(this._activetok_ == child)
        {
            this._activetok_ = null;
            return;
        }

        throw new RuntimeException("Not a child.");
    }

    @Override
    void replaceChild(@SuppressWarnings("unused") Node oldChild, @SuppressWarnings("unused") Node newChild)
    {
        // Replace child
        if(this._activetok_ == oldChild)
        {
            setActivetok((TActivetok) newChild);
            return;
        }

        throw new RuntimeException("Not a child.");
    }
}
